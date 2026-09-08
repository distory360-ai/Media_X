import os
import logging
import asyncio
import asyncpg
import httpx
from textblob import TextBlob
from datetime import datetime
from typing import Optional, List
import urllib.parse
from dateutil import parser as date_parser

# Structured logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s"
)
logger = logging.getLogger("MediaPulseXCollector")


class MediaPulseXCollector:
    BASE_URL = "https://api.twitterapi.io/twitter/tweet/advanced_search"
    MAX_RETRIES = 5
    BATCH_SIZE = 100

    def __init__(self, api_key: str, db_url: str):
        self.api_key = api_key
        self.db_url = db_url
        self.pool: Optional[asyncpg.Pool] = None

    async def init_pool(self):
        """Initialises database connection pool once."""
        if not self.pool:
            self.pool = await asyncpg.create_pool(
                dsn=self.db_url,
                min_size=2,
                max_size=10,
                command_timeout=30
            )
            logger.info("Database connection pool initialised.")

    async def close_pool(self):
        """Closes database pool gracefully."""
        if self.pool:
            await self.pool.close()
            logger.info("Database connection pool closed.")

    @staticmethod
    def get_sentiment(text: str) -> tuple[str, float]:
        score = TextBlob(text).sentiment.polarity
        label = "Positive" if score > 0 else ("Negative" if score < 0 else "Neutral")
        return label, round(score, 4)

    @staticmethod
    def parse_timestamp(raw_ts: str) -> Optional[datetime]:
        """Parses multiple timestamp formats safely without failing to NULL."""
        if not raw_ts:
            return None
        
        # 1. Standard Twitter string format
        try:
            return datetime.strptime(raw_ts, "%a %b %d %H:%M:%S +0000 %Y")
        except (ValueError, TypeError):
            pass

        # 2. ISO 8601 string (e.g. 2026-09-08T14:11:05Z)
        try:
            return date_parser.parse(raw_ts)
        except Exception:
            pass

        # 3. Numeric Epoch timestamp
        try:
            return datetime.utcfromtimestamp(float(raw_ts))
        except (ValueError, TypeError):
            return None

    async def _batch_save(self, records: list[tuple]):
        if not records or not self.pool:
            return
        async with self.pool.acquire() as conn:
            await conn.executemany(
                """
                INSERT INTO social_media_feeds
                    (tweet_id, content, author, created_at,
                     sentiment, sentiment_score, follower_count, user_location)
                VALUES ($1,$2,$3,$4,$5,$6,$7,$8)
                ON CONFLICT (tweet_id) DO NOTHING
                """,
                records
            )
        logger.info(f"Batch saved {len(records)} tweets.")

    async def _fetch_page(
        self,
        client: httpx.AsyncClient,
        params: dict,
        attempt: int = 0
    ) -> Optional[dict]:
        try:
            response = await client.get(
                self.BASE_URL,
                headers={"X-API-Key": self.api_key},
                params=params,
                timeout=15
            )

            if response.status_code == 200:
                return response.json()

            if response.status_code == 429:  # Rate limited
                wait = 2 ** attempt
                logger.warning(f"Rate limited. Retrying in {wait}s (attempt {attempt+1}/{self.MAX_RETRIES})")
                await asyncio.sleep(wait)
                if attempt < self.MAX_RETRIES:
                    return await self._fetch_page(client, params, attempt + 1)

            logger.error(f"API error {response.status_code}: {response.text[:200]}")
            return None

        except httpx.RequestError as e:
            logger.error(f"Network error: {e}")
            if attempt < self.MAX_RETRIES:
                await asyncio.sleep(2 ** attempt)
                return await self._fetch_page(client, params, attempt + 1)
            return None

    async def run_ingestion(self, keywords: List[str]):
        """Runs ingestion across list of targeted search query strings."""
        await self.init_pool()
        total_overall = 0

        async with httpx.AsyncClient() as client:
            for keyword in keywords:
                logger.info(f"--- Starting ingestion for query: {keyword} ---")
                query_total = 0
                next_cursor = None

                while True:
                    params = {
                        "query": keyword,
                        "queryType": "Latest",
                        "count": 100
                    }
                    if next_cursor:
                        params["cursor"] = next_cursor

                    data = await self._fetch_page(client, params)
                    if not data:
                        break

                    tweets = data.get("tweets", [])
                    if not tweets:
                        logger.info(f"No tweets returned for query '{keyword}'. Moving to next query.")
                        break

                    batch = []
                    for tweet in tweets:
                        try:
                            text = tweet.get("text", "")
                            user = tweet.get("author", {})
                            sentiment, score = self.get_sentiment(text)
                            raw_ts = tweet.get("createdAt", "") or tweet.get("created_at", "")
                            created_at = self.parse_timestamp(str(raw_ts))

                            batch.append((
                                str(tweet["id"]),
                                text,
                                str(user.get("id", "")),
                                created_at,
                                sentiment,
                                score,
                                user.get("followersCount", 0),
                                user.get("location", "Unknown")
                            ))
                        except KeyError as e:
                            logger.warning(f"Skipping malformed tweet — missing field: {e}")

                    await self._batch_save(batch)
                    query_total += len(batch)

                    next_cursor = data.get("next_cursor") or data.get("nextCursor")
                    if not next_cursor:
                        break

                    logger.info(f"Query '{keyword}': Saved {query_total} tweets so far. Fetching next page...")
                    await asyncio.sleep(0.5)

                total_overall += query_total
                logger.info(f"Completed query '{keyword}'. Total saved: {query_total}")

        logger.info(f"=== Ingestion process completed. Total overall tweets saved: {total_overall} ===")


# Chunked Search Target Queries (prevents twitterapi.io 0-result query failure)
TARGETS = [
    "(#TechInAfrica OR #AfricaTech OR #NairobiTech OR #LagosTech OR #CapeTownTech) -filter:retweets lang:en",
    "(#AfricanStartups OR #AfricanSummit OR #AI OR #AMR) -filter:retweets lang:en",
    "(@SafaricomPLC OR @MTNGroup OR @DangoteGroup OR @KCBGroup OR @EquityBank) -filter:retweets lang:en",
    "(@AbsaSouthAfrica OR @NCBABankKenya OR @KenyattaNationalHospital) -filter:retweets lang:en",
    "(@MastercardAfricacentreforinnovativeteachingandlearning OR @MastercardAfricascholars) -filter:retweets lang:en"
]

if __name__ == "__main__":
    key = os.getenv("X_BEARER_TOKEN")
    raw_db_url = os.getenv("DATABASE_URL")

    if not key or not raw_db_url:
        raise ValueError("FATAL: Missing environment variables (X_BEARER_TOKEN, DATABASE_URL)")

    # Parse and encode connection password if special characters exist
    parsed = urllib.parse.urlparse(raw_db_url)
    if parsed.password:
        encoded_password = urllib.parse.quote_plus(parsed.password)
        netloc = f"{parsed.username}:{encoded_password}@{parsed.hostname}"
        if parsed.port:
            netloc += f":{parsed.port}"
        db_url = parsed._replace(netloc=netloc).geturl()
    else:
        db_url = raw_db_url

    collector = MediaPulseXCollector(api_key=key, db_url=db_url)
    
    try:
        asyncio.run(collector.run_ingestion(keywords=TARGETS))
    finally:
        asyncio.run(collector.close_pool())

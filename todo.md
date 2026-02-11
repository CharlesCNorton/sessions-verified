# sessions-verified — Implementation Plan

## Layer 0: Foundations (Z-based time arithmetic)

1. Use `Z` (binary integers) throughout, not `nat`. Import `ZArith`, `Lia`. Set extraction to `ExtrOcamlZInt` so Z maps to OCaml `int` with no unary penalty.
2. Define `instant : Type := Z` as signed microseconds since the Unix epoch (1970-01-01T00:00:00Z). Prove `instant` has decidable equality and a total order via `Z.compare`.
3. Define `duration : Type := Z` as signed microseconds. Prove `duration` forms an abelian group under addition. Prove `instant + duration = instant` and `instant - instant = duration` with the expected cancellation laws.
4. Define `ceil_div_Z` and `floor_div_Z` for Z with explicit rounding-direction proofs. Prove `floor_div_Z a b * b <= a < floor_div_Z a b * b + b` for `b > 0`. Prove `ceil_div_Z a b * b >= a > ceil_div_Z a b * b - b` for `b > 0`. These are the workhorses for bar alignment.
5. Prove that `Z.compare` on instants is reflexive, antisymmetric, and transitive as standalone lemmas (not relying on lia inside later proofs).
6. Define `interval := { iv_start : instant ; iv_end : instant ; iv_wf : iv_start <= iv_end }` as a sigma type. Prove that intervals have decidable membership (`iv_start <= t <= iv_end` is decidable), decidable overlap, decidable containment, and decidable disjointness.
7. Prove interval arithmetic: `iv_duration iv = iv_end iv - iv_start iv >= 0`. Prove that splitting an interval at a point `t` inside it yields two intervals whose durations sum to the original.
8. Define `covers (intervals : list interval) (outer : interval) : Prop` asserting that every instant in `outer` belongs to at least one interval in the list. Define `partitions (intervals : list interval) (outer : interval) : Prop` asserting `covers` plus pairwise disjointness (except at shared endpoints). These are the central structural predicates — bars must partition sessions, sessions must partition trading days.

## Layer 1: Gregorian Calendar

9. Define `year`, `month` (1–12), `day` (1–31), `hour` (0–23), `minute` (0–59), `second` (0–59), `microsecond` (0–999999) as Z-valued types with range predicates.
10. Define `is_leap_year (y : Z) : bool` implementing the 400/100/4 rule. Prove `is_leap_year 2000 = true`, `is_leap_year 1900 = false`, `is_leap_year 2024 = true`, `is_leap_year 2023 = false` by computation.
11. Define `days_in_month (y : Z) (m : Z) : Z` returning 28/29/30/31. Prove it is always in `{28, 29, 30, 31}`. Prove `days_in_month y 2 = 29 <-> is_leap_year y = true`.
12. Define `days_in_year (y : Z) : Z` as the sum of `days_in_month` over 12 months. Prove `days_in_year y = 365 + (if is_leap_year y then 1 else 0)`.
13. Define `valid_date (y m d : Z) : Prop := 1 <= m <= 12 /\ 1 <= d <= days_in_month y m`. Prove decidability.
14. Define `date_to_epoch_days (y m d : Z) : Z` mapping a Gregorian date to days since 1970-01-01. Use the algorithm from Howard Hinnant's `chrono`-compatible date formulas (the `days_from_civil` algorithm) which is branch-free and proven correct for all dates from year -32768 to 32767. Prove injectivity: `date_to_epoch_days y1 m1 d1 = date_to_epoch_days y2 m2 d2 -> (y1,m1,d1) = (y2,m2,d2)` for valid dates.
15. Define `epoch_days_to_date (days : Z) : Z * Z * Z` as the inverse. Prove `epoch_days_to_date (date_to_epoch_days y m d) = (y, m, d)` for all valid dates. Prove `date_to_epoch_days (epoch_days_to_date d) = d` (where the triple is destructured). This round-trip pair is the calendar kernel — every later layer depends on it.
16. Define `datetime_to_instant (y m d h min s us : Z) : instant` composing date-to-epoch-days with time-of-day arithmetic: `date_to_epoch_days y m d * 86400000000 + h * 3600000000 + min * 60000000 + s * 1000000 + us`. Prove this is strictly monotone in the lexicographic order of `(y, m, d, h, min, s, us)`.
17. Define `instant_to_datetime (t : instant) : Z * Z * Z * Z * Z * Z * Z` as the inverse. Prove the full round-trip in both directions.
18. Define `day_of_week (y m d : Z) : Z` (0 = Monday, 6 = Sunday) using Tomohiko Sakamoto's algorithm or equivalent. Prove `day_of_week` is consistent with `date_to_epoch_days`: `day_of_week y m d = (date_to_epoch_days y m d + 3) mod 7` (since 1970-01-01 was a Thursday = day 3). Prove the range is always 0–6.

## Layer 2: Time Zones and DST

19. Define `utc_offset : Type := Z` as signed minutes from UTC (e.g., EST = -300, JST = +540). Prove that applying an offset and its negation is the identity: `t + offset * 60000000 - offset * 60000000 = t`.
20. Define a `tz_transition` record: `{ tt_at : instant ; tt_offset_before : utc_offset ; tt_offset_after : utc_offset }`. This is a single DST or zone-rule change at a specific UTC instant. `tt_at` is the exact UTC microsecond when the new offset takes effect.
21. Define `tz_rule : Type := list tz_transition` as a sorted (by `tt_at`) list of transitions. Define `tz_rule_sorted (r : tz_rule) : Prop` and `tz_rule_no_dup (r : tz_rule) : Prop` (no two transitions at the same instant). Bundle these into a `well_formed_tz_rule` record.
22. Define `utc_to_offset (r : tz_rule) (t : instant) : utc_offset` returning the active offset at UTC instant `t`. This is a pure lookup: find the last transition at or before `t`, return its `tt_offset_after`; if `t` precedes all transitions, return the `tt_offset_before` of the first transition. Prove this function is total — it returns a definite offset for every instant, with no option type.
23. Define `utc_to_local (r : tz_rule) (t : instant) : instant := t + utc_to_offset r t * 60000000`. Prove this is total.
24. Prove that `utc_to_local` is monotone within any contiguous offset interval (between consecutive transitions), but NOT globally monotone — demonstrate a counterexample at a fall-back transition where two distinct UTC instants map to the same local instant.
25. Define the DST gap predicate: `is_gap (r : tz_rule) (local_t : instant) : Prop` — a local time that corresponds to no UTC instant. This occurs during spring-forward: the local clock jumps from `tt_at + offset_before` to `tt_at + offset_after`, and times between those two local instants don't exist. Prove that gaps occur iff `tt_offset_after > tt_offset_before` for some transition.
26. Define the DST overlap predicate: `is_overlap (r : tz_rule) (local_t : instant) : Prop` — a local time that corresponds to two distinct UTC instants. This occurs during fall-back. Prove overlaps occur iff `tt_offset_after < tt_offset_before`.
27. Define `local_to_utc (r : tz_rule) (local_t : instant) : instant` as the *total* inverse of `utc_to_local`. For gaps, snap forward to the first valid local instant after the gap. For overlaps, choose the *later* UTC instant (i.e., prefer the new offset). Document and prove both choices. Prove `local_to_utc r (utc_to_local r t) = t` for all `t` (the round-trip from UTC is exact). Prove that `utc_to_local r (local_to_utc r lt) = lt` when `lt` is not in a gap.
28. Prove the gap/overlap classification theorem: for every local instant `lt` and well-formed tz_rule `r`, exactly one of three cases holds: (a) `lt` is in a gap, (b) `lt` is in an overlap, (c) `lt` corresponds to exactly one UTC instant. This is the totality-of-classification theorem.
29. Encode concrete tz_rules for at least: `America/New_York` (EST/EDT), `America/Chicago` (CST/CDT), `Europe/London` (GMT/BST), `Asia/Tokyo` (JST, no DST), `Asia/Hong_Kong` (HKT, no DST), `Australia/Sydney` (AEST/AEDT, southern hemisphere DST). Include transitions for at least 2020–2030. Prove each is `well_formed_tz_rule`.

## Layer 3: Holiday Calendars

30. Define `holiday_calendar : Type := list (Z * Z * Z)` as a sorted list of `(year, month, day)` triples. Define `well_formed_calendar` requiring sorted order, valid dates, and no duplicates.
31. Define `is_holiday (cal : holiday_calendar) (y m d : Z) : bool` by sorted binary search. Prove decidability and correctness: `is_holiday cal y m d = true <-> In (y, m, d) cal`.
32. Define `is_weekend (y m d : Z) : bool := day_of_week y m d >=? 5`. Prove correctness.
33. Define `is_business_day (cal : holiday_calendar) (y m d : Z) : bool := negb (is_weekend y m d) && negb (is_holiday cal y m d)`. Prove decidability.
34. Define `next_business_day` and `prev_business_day` that skip weekends and holidays. Prove termination (the gap between consecutive business days is at most 9 for any holiday calendar where holidays don't span more than 5 consecutive weekdays — state this as a hypothesis; or prove unconditional termination by bounding the search to 366 days and proving a business day must exist within any 10-day window given the weekend structure). Prove `next_business_day` returns a strictly later date. Prove `prev_business_day` returns a strictly earlier date.
35. Define `count_business_days (cal : holiday_calendar) (start_date end_date : Z * Z * Z) : Z`. Prove it equals the cardinality of `{d | start_date <= d <= end_date /\ is_business_day cal d = true}`. Prove monotonicity: extending the range cannot decrease the count.
36. Encode concrete holiday calendars for at least: NYSE, NASDAQ, CME, LSE, TSE (Tokyo), HKEX, ASX. Include holidays for 2020–2030. For each, prove `well_formed_calendar`.
37. Define holiday observation rules: `observed_holiday` handling Saturday→Friday and Sunday→Monday shifts for US markets. Prove that observed holidays are valid dates and that the observation function is idempotent.

## Layer 4: Trading Sessions

38. Define `session_template` record: `{ st_open_offset : duration ; st_close_offset : duration ; st_open_lt_close : st_open_offset < st_close_offset }`. Offsets are microseconds from midnight local time. The sigma type enforces open < close.
39. Define `early_close_template` record: same as `session_template` but with `st_close_offset` earlier than the regular close. Carry a proof that the early close is between open and regular close.
40. Define `trading_calendar` record bundling: `{ tc_tz : tz_rule ; tc_holidays : holiday_calendar ; tc_regular : session_template ; tc_early_closes : list (Z * Z * Z * early_close_template) ; tc_pre_market : option session_template ; tc_after_hours : option session_template }`.
41. Define `session_for_date (tc : trading_calendar) (y m d : Z) : option interval`. Returns `None` if the date is a weekend or holiday. Returns `Some iv` where `iv` is the UTC interval `[open_utc, close_utc)` computed by converting local open/close times through `local_to_utc` using `tc_tz`. If the date appears in `tc_early_closes`, use the early close time. Prove: when the result is `Some iv`, `iv_start iv < iv_end iv` (nondegenerate session).
42. Prove totality of session classification: for every UTC instant `t`, define `session_status (tc : trading_calendar) (t : instant)` returning one of: `InRegularSession date`, `InPreMarket date`, `InAfterHours date`, `Closed`. Prove this classification is total — every instant gets exactly one status. Prove decidability.
43. Prove session non-overlap: for a well-formed `trading_calendar`, no two sessions (regular, pre-market, after-hours) for any date overlap with each other or with sessions of adjacent dates. This requires proving that the after-hours session ends before the next day's pre-market session begins, etc. State the required separation hypotheses explicitly.
44. Prove that consecutive regular sessions for consecutive business days have a positive gap between them (closed period exists). Prove the closed period duration is always at least `24*60*60*1000000 - (close_offset - open_offset)` microseconds minus any DST shift.
45. Prove DST-session interaction theorems: (a) a spring-forward during a session shortens it by the gap duration; (b) a fall-back during a session lengthens it by the overlap duration; (c) if a spring-forward gap contains the local open time, the session starts at the first valid local instant after the gap (inherited from `local_to_utc` behavior). Prove that in all three cases the session interval is still nondegenerate.
46. Define `sessions_in_range (tc : trading_calendar) (start end_ : instant) : list (Z * Z * Z * interval)` returning all `(year, month, day, session_interval)` pairs whose session intersects `[start, end_)`. Prove: (a) the returned list is sorted by session start; (b) the session intervals are pairwise disjoint; (c) every returned interval intersects `[start, end_)`; (d) no session intersecting `[start, end_)` is omitted.

## Layer 5: Bar and Window Bucketing

47. Define `bar_width : Type := { bw_us : Z ; bw_pos : bw_us > 0 }`. Common widths: 1-second (1000000), 1-minute (60000000), 5-minute (300000000), 15-minute, 30-minute, 1-hour, 4-hour, 1-day.
48. Define `bar_index (bw : bar_width) (session_start : instant) (t : instant) : Z := floor_div_Z (t - session_start) (bw_us bw)`. This assigns every instant within a session to a bar number. Prove: `bar_index` is monotone (later instants get equal or higher index). Prove: two instants in the same bar have `|t1 - t2| < bw_us bw`.
49. Define `bar_interval (bw : bar_width) (session_start : instant) (idx : Z) : interval` returning the half-open interval `[session_start + idx * bw_us, session_start + (idx + 1) * bw_us)`. Prove: `bar_interval` produces a valid interval (start < end). Prove: `t` falls in `bar_interval bw session_start (bar_index bw session_start t)` for all `t >= session_start`.
50. Prove the bar partition theorem: for a session interval `[open, close)` and bar width `bw`, the bars `bar_interval bw open 0`, `bar_interval bw open 1`, ..., `bar_interval bw open (n-1)` partition the session, where `n = ceil_div_Z (close - open) (bw_us bw)`. Prove: (a) every instant in `[open, close)` falls in exactly one bar; (b) bars are pairwise disjoint; (c) bars are contiguous (bar k's end = bar k+1's start); (d) the first bar starts at `open`; (e) the last bar ends at or after `close`.
51. Prove the partial-bar theorem: if `(close - open)` is not divisible by `bw_us bw`, the last bar extends past `close`. Compute the partial bar's effective duration as `(close - open) mod (bw_us bw)`. Prove this is strictly between 0 and `bw_us bw`. Define `bar_count` as `ceil_div_Z (close - open) (bw_us bw)` and prove it equals the number of bars covering the session.
52. Define `session_bar_index (tc : trading_calendar) (bw : bar_width) (t : instant) : option (Z * Z * Z * Z)` returning `Some (year, month, day, bar_idx)` if `t` is in a regular session, `None` otherwise. Prove totality of the composed classification: every instant either gets a `(date, bar)` or is confirmed out-of-session.
53. Define `bar_boundaries (tc : trading_calendar) (bw : bar_width) (y m d : Z) : list instant` returning the bar-boundary instants for a given session date. Prove: (a) the list is sorted; (b) the first element equals the session open; (c) consecutive elements differ by exactly `bw_us bw` except possibly the last pair; (d) the last element equals or exceeds the session close.
54. Prove cross-session bar independence: bars from different sessions never share an instant (they're separated by the closed period). This follows from session non-overlap (item 43) but state and prove it as a standalone corollary.
55. Define multi-day bar aggregation: `daily_bar (tc : trading_calendar) (y m d : Z)` as the single bar spanning the entire session. Prove `daily_bar` is a special case of `bar_interval` with `bw_us = close - open`. Prove the daily bar count is always 1.
56. Define `vwap_window (tc : trading_calendar) (t : instant) (lookback : duration) : interval` returning the interval `[max(session_open, t - lookback), t]` clipped to the current session. Prove: (a) the result is a valid interval; (b) it is contained within the current session; (c) its duration is `min(lookback, t - session_open)`.

## Layer 6: Parameterization and Abstraction

57. Wrap Layers 0–5 in a parameterized `Section` over the `trading_calendar`. All theorems should hold for any well-formed calendar, not just the hardcoded exchange instances.
58. Define a `well_formed_trading_calendar` record bundling all required hypotheses: tz_rule sorted and no-dup, holiday calendar sorted and valid, session templates valid, early closes are subsets of business days, pre-market ends before regular open, after-hours starts after regular close, etc. Prove that each concrete exchange instance satisfies `well_formed_trading_calendar`.
59. Define an abstract `exchange` Module Type exposing: `tz_rule`, `holiday_calendar`, `session_template`, `early_close_template`, plus all well-formedness proofs. Provide concrete Module implementations for NYSE, NASDAQ, CME, LSE, TSE, HKEX, ASX.

## Layer 7: Extraction and OCaml Interface

60. Add `Require Import Extraction`, `ExtrOcamlBasic`, `ExtrOcamlZInt`. Extract all of: `utc_to_local`, `local_to_utc`, `utc_to_offset`, `session_for_date`, `session_status`, `bar_index`, `bar_interval`, `bar_count`, `bar_boundaries`, `session_bar_index`, `sessions_in_range`, `daily_bar`, `vwap_window`, `is_business_day`, `next_business_day`, `prev_business_day`, `count_business_days`, `instant_to_datetime`, `datetime_to_instant`, `day_of_week`, `detect_gaps` (for DST gap detection).
61. Verify that NO extracted function returns an `option` for a query that the formalization proves total. The extracted type signatures must reflect totality: `session_status` returns a sum type with no `None` branch, `bar_index` returns `Z`, `utc_to_offset` returns `Z`. Any extracted `option` must correspond to a genuinely partial operation (e.g., `session_for_date` on a holiday).
62. Write a hand-crafted `.mli` hiding extraction internals (Z representation, positives, etc.), exposing only the public API with OCaml-native types (`int` for microsecond instants, `int` for offsets, etc.).
63. Write an OCaml functor `Session_functor.Make(E : EXCHANGE)` wrapping the extracted functions. `EXCHANGE` provides: `tz_transitions`, `holidays`, `session_open`, `session_close`, `early_closes`. The functor instantiates the parameterized Coq code.
64. Add `validate` at the functor boundary rejecting instants outside the supported transition range (e.g., before 2020 or after 2030 if only those transitions are encoded) and rejecting years outside the holiday calendar range. Raise `Invalid_argument` with a descriptive message.

## Layer 8: Tests

65. Write round-trip unit tests for `datetime_to_instant` / `instant_to_datetime` covering: epoch (1970-01-01T00:00:00Z), leap day (2024-02-29), end of year (2023-12-31T23:59:59.999999Z), negative years, dates before/after epoch.
66. Write DST transition tests for `America/New_York`: (a) spring-forward 2024-03-10T02:00 EST → 03:00 EDT, verify the gap is detected, verify `local_to_utc` snaps forward; (b) fall-back 2024-11-03T02:00 EDT → 01:00 EST, verify the overlap is detected, verify `local_to_utc` picks the later UTC instant.
67. Write session tests for NYSE: (a) regular session 2024-01-02 (first trading day of year) opens 9:30 ET, closes 16:00 ET, verify UTC intervals; (b) early close 2024-07-03 (day before July 4th) closes 13:00 ET; (c) holiday 2024-07-04 returns no session; (d) weekend 2024-01-06 (Saturday) returns no session.
68. Write bar bucketing tests: (a) 1-minute bars on a 6.5-hour NYSE session yield exactly 390 bars; (b) 5-minute bars yield 78 bars; (c) bar 0 starts at 9:30, bar 1 starts at 9:31 (for 1-min bars); (d) the last bar's effective end equals 16:00.
69. Write a DST-session interaction test: pick a date where spring-forward occurs during pre-market hours (e.g., 2024-03-10 for NYSE). Verify the pre-market session is shortened. Verify the regular session is unaffected. Verify bar counts adjust.
70. Write a random stress test (1000+ trials): generate random UTC instants in [2020, 2030), classify via `session_status`, verify the classification is consistent with `session_for_date` for the same date, verify bar indices are non-negative and bounded by `bar_count`.
71. Write a property test: for 1000 random business days across all 7 exchanges, verify that `sessions_in_range` over a 24-hour window centered on noon returns exactly one session (or zero for holidays), that the session interval is nondegenerate, and that bar boundaries partition it.
72. Write an exhaustive DST-boundary test: for every transition in every encoded tz_rule (2020–2030), generate instants at `transition - 1us`, `transition`, and `transition + 1us`, verify `utc_to_offset` returns the correct offset at each, and verify `utc_to_local` produces the expected local time.

## Layer 9: Hardening

73. Prove that all `Fixpoint` and `Function` definitions used in extraction pass Coq's guard checker on structural arguments (no fuel parameters, no `Program Fixpoint` with opaque obligations). Every recursive function must have a structurally decreasing argument visible in the type.
74. Prove that `bar_index` never produces a negative index for `t >= session_start`. Prove that `bar_index` never exceeds `bar_count - 1` for `t < session_close`.
75. Prove the microsecond-precision round-trip: `instant_to_datetime (datetime_to_instant y m d h min s us) = (y, m, d, h, min, s, us)` for all valid 7-tuples, and the converse. This is the ultimate test of the calendar kernel — no off-by-one, no rounding, no truncation.
76. Prove that `utc_to_offset` is piecewise constant: it changes value only at transition instants. Formally: if `t1 < t2` and there is no transition `tt_at` with `t1 < tt_at <= t2`, then `utc_to_offset r t1 = utc_to_offset r t2`.
77. Prove that `sessions_in_range` is idempotent under re-query: querying the range `[min(starts), max(ends))` of the returned sessions returns the same list.
78. Prove that `local_to_utc` composed with `utc_to_local` is the identity: `local_to_utc r (utc_to_local r t) = t` for all `t`. Prove separately that `utc_to_local r (local_to_utc r lt) = lt` when `lt` is not in a DST gap, and characterize the snap behavior when it is.
79. Prove that the total ordering on instants is preserved through bar indexing: if `t1 < t2` and both are in the same session, then `bar_index bw open t1 <= bar_index bw open t2`. Prove strict inequality iff `t1` and `t2` are in different bars.
80. Prove all `Defined` (not `Qed`) for every lemma used transitively by an extracted function. Any `Qed` in the dependency chain of an extracted function blocks computation and must be replaced.

## Layer 10: Documentation and Build

81. Write a `README.md` with: problem statement (why market time is hard), trust boundary table (verified vs. unverified), proven properties table with theorem names, event model, API reference, building instructions.
82. Write a `USAGE.md` with functor instantiation example, API table with complexity annotations, and trust boundary explanation.
83. Write a `Makefile` with targets: `extract` (coqc → .ml), `test` (OCaml unit tests), `test-random` (property tests), `test-dst` (DST boundary tests), `bench` (throughput benchmark for bar classification), `clean`, `all`.
84. Add a `.gitignore` excluding: `*.vo`, `*.vos`, `*.vok`, `*.glob`, `*.aux`, `.lia.cache`, `*.cmo`, `*.cmi`, `*.exe`, `build/`, `_build/`, `*.byte`, `*.native`.
85. Ensure the final line count of `sessions.v` is documented in the README. Target: the formalization should be self-contained in a single `.v` file (no Coq library dependencies beyond the standard library and ZArith).

---
title: "Lab02: Selection Sort (part 1) and `≤` on `Answer`"
date: 2023-02-06T16:43:57+05:30
draft: false
---

Before doing this assignment you will need to pull from the upstream repository, i.e., the course repository. Please complete the definitions/proofs in the files `PnP2023/Labs/Lab02/SelectionSort.lean` and `PnP2023/Labs/Lab02/AnswerLE.lean`. When you are done please commit and push your changes to your forked private repository and alert me on Zulip.

1. Complete the proof of `remove_length_le` in `PnP2023/Labs/Lab02/SelectionSort.lean`.

2. Complete the proof of `remove_mem_length` in `PnP2023/Labs/Lab02/SelectionSort.lean`.

3. Complete the definition of `selectionSort` in `PnP2023/Labs/Lab02/SelectionSort.lean`, including proof by termination. Do not make this a `partial def`. Also ensure that there is no error saying that you failed to prove termination.

4. Complete the proof of `Answer.eq_of_le_le` in `PnP2023/Labs/Lab02/AnswerLE.lean`.
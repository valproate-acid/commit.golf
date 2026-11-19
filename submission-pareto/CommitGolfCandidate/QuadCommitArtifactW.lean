import CommitGolfCandidate.QuadCommitWalk_leaf0
import CommitGolfCandidate.QuadCommitWalk_leaf1
import CommitGolfCandidate.QuadCommitWalk_leaf2
import CommitGolfCandidate.QuadCommitWalk_leaf3
import CommitGolfCandidate.QuadCommitWalk_node0
import CommitGolfCandidate.QuadCommitWalk_node1
import CommitGolfCandidate.QuadCommitWalk_node2
import CommitGolfCandidate.QuadCommitWalk_node3
import CommitGolfCandidate.QuadCommitWalk_node4
import CommitGolfCandidate.QuadCommitWalk_node5
import CommitGolfCandidate.QuadCommitWalk_node6
import CommitGolfCandidate.QuadCommitWalk_node7
namespace TwoPermutationPrototype.ArtifactMatchB
open CommitGolf Quad.Commit
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem walk_range_join (g : Nat → List (BitVec 32)) (i j k s m c : Nat)
    (first : walk 32 Artifact.commitCode g i (List.range' s m) = some j)
    (rest : walk 32 Artifact.commitCode g j (List.range' (s + m) c) = some k) :
    walk 32 Artifact.commitCode g i (List.range' s (m + c)) = some k := by
  rw [range'_split]; exact walk_append 32 _ g _ _ i j k first rest

theorem leaf_from_3968 : walk 32 Artifact.commitCode leafWords 43771 (List.range' 3968 128) = some 45183 :=
  leaf_block_3968
theorem leaf_from_3840 : walk 32 Artifact.commitCode leafWords 42359 (List.range' 3840 256) = some 45183 :=
  walk_range_join leafWords 42359 43771 45183 3840 128 128 leaf_block_3840 leaf_from_3968
theorem leaf_from_3712 : walk 32 Artifact.commitCode leafWords 40948 (List.range' 3712 384) = some 45183 :=
  walk_range_join leafWords 40948 42359 45183 3712 128 256 leaf_block_3712 leaf_from_3840
theorem leaf_from_3584 : walk 32 Artifact.commitCode leafWords 39536 (List.range' 3584 512) = some 45183 :=
  walk_range_join leafWords 39536 40948 45183 3584 128 384 leaf_block_3584 leaf_from_3712
theorem leaf_from_3456 : walk 32 Artifact.commitCode leafWords 38125 (List.range' 3456 640) = some 45183 :=
  walk_range_join leafWords 38125 39536 45183 3456 128 512 leaf_block_3456 leaf_from_3584
theorem leaf_from_3328 : walk 32 Artifact.commitCode leafWords 36713 (List.range' 3328 768) = some 45183 :=
  walk_range_join leafWords 36713 38125 45183 3328 128 640 leaf_block_3328 leaf_from_3456
theorem leaf_from_3200 : walk 32 Artifact.commitCode leafWords 35303 (List.range' 3200 896) = some 45183 :=
  walk_range_join leafWords 35303 36713 45183 3200 128 768 leaf_block_3200 leaf_from_3328
theorem leaf_from_3072 : walk 32 Artifact.commitCode leafWords 33891 (List.range' 3072 1024) = some 45183 :=
  walk_range_join leafWords 33891 35303 45183 3072 128 896 leaf_block_3072 leaf_from_3200
theorem leaf_from_2944 : walk 32 Artifact.commitCode leafWords 32480 (List.range' 2944 1152) = some 45183 :=
  walk_range_join leafWords 32480 33891 45183 2944 128 1024 leaf_block_2944 leaf_from_3072
theorem leaf_from_2816 : walk 32 Artifact.commitCode leafWords 31068 (List.range' 2816 1280) = some 45183 :=
  walk_range_join leafWords 31068 32480 45183 2816 128 1152 leaf_block_2816 leaf_from_2944
theorem leaf_from_2688 : walk 32 Artifact.commitCode leafWords 29657 (List.range' 2688 1408) = some 45183 :=
  walk_range_join leafWords 29657 31068 45183 2688 128 1280 leaf_block_2688 leaf_from_2816
theorem leaf_from_2560 : walk 32 Artifact.commitCode leafWords 28245 (List.range' 2560 1536) = some 45183 :=
  walk_range_join leafWords 28245 29657 45183 2560 128 1408 leaf_block_2560 leaf_from_2688
theorem leaf_from_2432 : walk 32 Artifact.commitCode leafWords 26835 (List.range' 2432 1664) = some 45183 :=
  walk_range_join leafWords 26835 28245 45183 2432 128 1536 leaf_block_2432 leaf_from_2560
theorem leaf_from_2304 : walk 32 Artifact.commitCode leafWords 25423 (List.range' 2304 1792) = some 45183 :=
  walk_range_join leafWords 25423 26835 45183 2304 128 1664 leaf_block_2304 leaf_from_2432
theorem leaf_from_2176 : walk 32 Artifact.commitCode leafWords 24012 (List.range' 2176 1920) = some 45183 :=
  walk_range_join leafWords 24012 25423 45183 2176 128 1792 leaf_block_2176 leaf_from_2304
theorem leaf_from_2048 : walk 32 Artifact.commitCode leafWords 22600 (List.range' 2048 2048) = some 45183 :=
  walk_range_join leafWords 22600 24012 45183 2048 128 1920 leaf_block_2048 leaf_from_2176
theorem leaf_from_1920 : walk 32 Artifact.commitCode leafWords 21189 (List.range' 1920 2176) = some 45183 :=
  walk_range_join leafWords 21189 22600 45183 1920 128 2048 leaf_block_1920 leaf_from_2048
theorem leaf_from_1792 : walk 32 Artifact.commitCode leafWords 19777 (List.range' 1792 2304) = some 45183 :=
  walk_range_join leafWords 19777 21189 45183 1792 128 2176 leaf_block_1792 leaf_from_1920
theorem leaf_from_1664 : walk 32 Artifact.commitCode leafWords 18366 (List.range' 1664 2432) = some 45183 :=
  walk_range_join leafWords 18366 19777 45183 1664 128 2304 leaf_block_1664 leaf_from_1792
theorem leaf_from_1536 : walk 32 Artifact.commitCode leafWords 16955 (List.range' 1536 2560) = some 45183 :=
  walk_range_join leafWords 16955 18366 45183 1536 128 2432 leaf_block_1536 leaf_from_1664
theorem leaf_from_1408 : walk 32 Artifact.commitCode leafWords 15544 (List.range' 1408 2688) = some 45183 :=
  walk_range_join leafWords 15544 16955 45183 1408 128 2560 leaf_block_1408 leaf_from_1536
theorem leaf_from_1280 : walk 32 Artifact.commitCode leafWords 14132 (List.range' 1280 2816) = some 45183 :=
  walk_range_join leafWords 14132 15544 45183 1280 128 2688 leaf_block_1280 leaf_from_1408
theorem leaf_from_1152 : walk 32 Artifact.commitCode leafWords 12721 (List.range' 1152 2944) = some 45183 :=
  walk_range_join leafWords 12721 14132 45183 1152 128 2816 leaf_block_1152 leaf_from_1280
theorem leaf_from_1024 : walk 32 Artifact.commitCode leafWords 11309 (List.range' 1024 3072) = some 45183 :=
  walk_range_join leafWords 11309 12721 45183 1024 128 2944 leaf_block_1024 leaf_from_1152
theorem leaf_from_896 : walk 32 Artifact.commitCode leafWords 9898 (List.range' 896 3200) = some 45183 :=
  walk_range_join leafWords 9898 11309 45183 896 128 3072 leaf_block_896 leaf_from_1024
theorem leaf_from_768 : walk 32 Artifact.commitCode leafWords 8487 (List.range' 768 3328) = some 45183 :=
  walk_range_join leafWords 8487 9898 45183 768 128 3200 leaf_block_768 leaf_from_896
theorem leaf_from_640 : walk 32 Artifact.commitCode leafWords 7076 (List.range' 640 3456) = some 45183 :=
  walk_range_join leafWords 7076 8487 45183 640 128 3328 leaf_block_640 leaf_from_768
theorem leaf_from_512 : walk 32 Artifact.commitCode leafWords 5664 (List.range' 512 3584) = some 45183 :=
  walk_range_join leafWords 5664 7076 45183 512 128 3456 leaf_block_512 leaf_from_640
theorem leaf_from_384 : walk 32 Artifact.commitCode leafWords 4253 (List.range' 384 3712) = some 45183 :=
  walk_range_join leafWords 4253 5664 45183 384 128 3584 leaf_block_384 leaf_from_512
theorem leaf_from_256 : walk 32 Artifact.commitCode leafWords 2841 (List.range' 256 3840) = some 45183 :=
  walk_range_join leafWords 2841 4253 45183 256 128 3712 leaf_block_256 leaf_from_384
theorem leaf_from_128 : walk 32 Artifact.commitCode leafWords 1430 (List.range' 128 3968) = some 45183 :=
  walk_range_join leafWords 1430 2841 45183 128 128 3840 leaf_block_128 leaf_from_256
theorem leaf_from_0 : walk 32 Artifact.commitCode leafWords 19 (List.range' 0 4096) = some 45183 :=
  walk_range_join leafWords 19 1430 45183 0 128 3968 leaf_block_0 leaf_from_128
theorem n1s_from_29184 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 132778 (List.range' 29184 246) = some 133516 :=
  n1s_block_29184
theorem n1s_from_28672 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 131242 (List.range' 28672 758) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 131242 132778 133516 28672 512 246 n1s_block_28672 n1s_from_29184
theorem n1s_from_28160 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 129706 (List.range' 28160 1270) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 129706 131242 133516 28160 512 758 n1s_block_28160 n1s_from_28672
theorem n1s_from_27648 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 128170 (List.range' 27648 1782) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 128170 129706 133516 27648 512 1270 n1s_block_27648 n1s_from_28160
theorem n1s_from_27136 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 126634 (List.range' 27136 2294) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 126634 128170 133516 27136 512 1782 n1s_block_27136 n1s_from_27648
theorem n1s_from_26624 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 125098 (List.range' 26624 2806) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 125098 126634 133516 26624 512 2294 n1s_block_26624 n1s_from_27136
theorem n1s_from_26112 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 123562 (List.range' 26112 3318) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 123562 125098 133516 26112 512 2806 n1s_block_26112 n1s_from_26624
theorem n1s_from_25600 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 122026 (List.range' 25600 3830) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 122026 123562 133516 25600 512 3318 n1s_block_25600 n1s_from_26112
theorem n1s_from_25088 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 120490 (List.range' 25088 4342) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 120490 122026 133516 25088 512 3830 n1s_block_25088 n1s_from_25600
theorem n1s_from_24576 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 118954 (List.range' 24576 4854) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 118954 120490 133516 24576 512 4342 n1s_block_24576 n1s_from_25088
theorem n1s_from_24064 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 117418 (List.range' 24064 5366) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 117418 118954 133516 24064 512 4854 n1s_block_24064 n1s_from_24576
theorem n1s_from_23552 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 115882 (List.range' 23552 5878) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 115882 117418 133516 23552 512 5366 n1s_block_23552 n1s_from_24064
theorem n1s_from_23040 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 114346 (List.range' 23040 6390) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 114346 115882 133516 23040 512 5878 n1s_block_23040 n1s_from_23552
theorem n1s_from_22528 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 112810 (List.range' 22528 6902) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 112810 114346 133516 22528 512 6390 n1s_block_22528 n1s_from_23040
theorem n1s_from_22016 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 111274 (List.range' 22016 7414) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 111274 112810 133516 22016 512 6902 n1s_block_22016 n1s_from_22528
theorem n1s_from_21504 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 109738 (List.range' 21504 7926) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 109738 111274 133516 21504 512 7414 n1s_block_21504 n1s_from_22016
theorem n1s_from_20992 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 108202 (List.range' 20992 8438) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 108202 109738 133516 20992 512 7926 n1s_block_20992 n1s_from_21504
theorem n1s_from_20480 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 106666 (List.range' 20480 8950) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 106666 108202 133516 20480 512 8438 n1s_block_20480 n1s_from_20992
theorem n1s_from_19968 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 105130 (List.range' 19968 9462) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 105130 106666 133516 19968 512 8950 n1s_block_19968 n1s_from_20480
theorem n1s_from_19456 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 103594 (List.range' 19456 9974) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 103594 105130 133516 19456 512 9462 n1s_block_19456 n1s_from_19968
theorem n1s_from_18944 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 102058 (List.range' 18944 10486) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 102058 103594 133516 18944 512 9974 n1s_block_18944 n1s_from_19456
theorem n1s_from_18432 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 100522 (List.range' 18432 10998) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 100522 102058 133516 18432 512 10486 n1s_block_18432 n1s_from_18944
theorem n1s_from_17920 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 98986 (List.range' 17920 11510) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 98986 100522 133516 17920 512 10998 n1s_block_17920 n1s_from_18432
theorem n1s_from_17408 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 97450 (List.range' 17408 12022) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 97450 98986 133516 17408 512 11510 n1s_block_17408 n1s_from_17920
theorem n1s_from_16896 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 95914 (List.range' 16896 12534) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 95914 97450 133516 16896 512 12022 n1s_block_16896 n1s_from_17408
theorem n1s_from_16384 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 94378 (List.range' 16384 13046) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 94378 95914 133516 16384 512 12534 n1s_block_16384 n1s_from_16896
theorem n1s_from_15872 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 92842 (List.range' 15872 13558) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 92842 94378 133516 15872 512 13046 n1s_block_15872 n1s_from_16384
theorem n1s_from_15360 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 91306 (List.range' 15360 14070) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 91306 92842 133516 15360 512 13558 n1s_block_15360 n1s_from_15872
theorem n1s_from_14848 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 89770 (List.range' 14848 14582) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 89770 91306 133516 14848 512 14070 n1s_block_14848 n1s_from_15360
theorem n1s_from_14336 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 88234 (List.range' 14336 15094) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 88234 89770 133516 14336 512 14582 n1s_block_14336 n1s_from_14848
theorem n1s_from_13824 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 86698 (List.range' 13824 15606) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 86698 88234 133516 13824 512 15094 n1s_block_13824 n1s_from_14336
theorem n1s_from_13312 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 85162 (List.range' 13312 16118) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 85162 86698 133516 13312 512 15606 n1s_block_13312 n1s_from_13824
theorem n1s_from_12800 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 83626 (List.range' 12800 16630) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 83626 85162 133516 12800 512 16118 n1s_block_12800 n1s_from_13312
theorem n1s_from_12288 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 82090 (List.range' 12288 17142) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 82090 83626 133516 12288 512 16630 n1s_block_12288 n1s_from_12800
theorem n1s_from_11776 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 80554 (List.range' 11776 17654) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 80554 82090 133516 11776 512 17142 n1s_block_11776 n1s_from_12288
theorem n1s_from_11264 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 79018 (List.range' 11264 18166) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 79018 80554 133516 11264 512 17654 n1s_block_11264 n1s_from_11776
theorem n1s_from_10752 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 77482 (List.range' 10752 18678) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 77482 79018 133516 10752 512 18166 n1s_block_10752 n1s_from_11264
theorem n1s_from_10240 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 75946 (List.range' 10240 19190) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 75946 77482 133516 10240 512 18678 n1s_block_10240 n1s_from_10752
theorem n1s_from_9728 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 74410 (List.range' 9728 19702) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 74410 75946 133516 9728 512 19190 n1s_block_9728 n1s_from_10240
theorem n1s_from_9216 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 72874 (List.range' 9216 20214) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 72874 74410 133516 9216 512 19702 n1s_block_9216 n1s_from_9728
theorem n1s_from_8704 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 71338 (List.range' 8704 20726) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 71338 72874 133516 8704 512 20214 n1s_block_8704 n1s_from_9216
theorem n1s_from_8192 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 69802 (List.range' 8192 21238) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 69802 71338 133516 8192 512 20726 n1s_block_8192 n1s_from_8704
theorem n1s_from_7680 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 68266 (List.range' 7680 21750) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 68266 69802 133516 7680 512 21238 n1s_block_7680 n1s_from_8192
theorem n1s_from_7168 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 66730 (List.range' 7168 22262) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 66730 68266 133516 7168 512 21750 n1s_block_7168 n1s_from_7680
theorem n1s_from_6656 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 65194 (List.range' 6656 22774) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 65194 66730 133516 6656 512 22262 n1s_block_6656 n1s_from_7168
theorem n1s_from_6144 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 63658 (List.range' 6144 23286) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 63658 65194 133516 6144 512 22774 n1s_block_6144 n1s_from_6656
theorem n1s_from_5632 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 62122 (List.range' 5632 23798) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 62122 63658 133516 5632 512 23286 n1s_block_5632 n1s_from_6144
theorem n1s_from_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 60586 (List.range' 5120 24310) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 60586 62122 133516 5120 512 23798 n1s_block_5120 n1s_from_5632
theorem n1s_from_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 59050 (List.range' 4608 24822) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 59050 60586 133516 4608 512 24310 n1s_block_4608 n1s_from_5120
theorem n1s_from_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 57514 (List.range' 4096 25334) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 57514 59050 133516 4096 512 24822 n1s_block_4096 n1s_from_4608
theorem n1s_from_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 55978 (List.range' 3584 25846) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 55978 57514 133516 3584 512 25334 n1s_block_3584 n1s_from_4096
theorem n1s_from_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 54442 (List.range' 3072 26358) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 54442 55978 133516 3072 512 25846 n1s_block_3072 n1s_from_3584
theorem n1s_from_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 52906 (List.range' 2560 26870) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 52906 54442 133516 2560 512 26358 n1s_block_2560 n1s_from_3072
theorem n1s_from_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 51370 (List.range' 2048 27382) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 51370 52906 133516 2048 512 26870 n1s_block_2048 n1s_from_2560
theorem n1s_from_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 49834 (List.range' 1536 27894) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 49834 51370 133516 1536 512 27382 n1s_block_1536 n1s_from_2048
theorem n1s_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 48298 (List.range' 1024 28406) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 48298 49834 133516 1024 512 27894 n1s_block_1024 n1s_from_1536
theorem n1s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 46762 (List.range' 512 28918) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 46762 48298 133516 512 512 28406 n1s_block_512 n1s_from_1024
theorem n1s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 45226 (List.range' 0 29430) = some 133516 :=
  walk_range_join (fun p => nodeWords (p % 5)) 45226 46762 133516 0 512 28918 n1s_block_0 n1s_from_512
theorem n1r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 133518 (List.range' 0 424) = some 134790 :=
  n1r_block_0
theorem n2s_from_14336 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 177811 (List.range' 14336 249) = some 178558 :=
  n2s_block_14336
theorem n2s_from_13824 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 176275 (List.range' 13824 761) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 176275 177811 178558 13824 512 249 n2s_block_13824 n2s_from_14336
theorem n2s_from_13312 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 174739 (List.range' 13312 1273) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 174739 176275 178558 13312 512 761 n2s_block_13312 n2s_from_13824
theorem n2s_from_12800 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 173203 (List.range' 12800 1785) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 173203 174739 178558 12800 512 1273 n2s_block_12800 n2s_from_13312
theorem n2s_from_12288 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 171667 (List.range' 12288 2297) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 171667 173203 178558 12288 512 1785 n2s_block_12288 n2s_from_12800
theorem n2s_from_11776 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 170131 (List.range' 11776 2809) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 170131 171667 178558 11776 512 2297 n2s_block_11776 n2s_from_12288
theorem n2s_from_11264 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 168595 (List.range' 11264 3321) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 168595 170131 178558 11264 512 2809 n2s_block_11264 n2s_from_11776
theorem n2s_from_10752 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 167059 (List.range' 10752 3833) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 167059 168595 178558 10752 512 3321 n2s_block_10752 n2s_from_11264
theorem n2s_from_10240 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 165523 (List.range' 10240 4345) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 165523 167059 178558 10240 512 3833 n2s_block_10240 n2s_from_10752
theorem n2s_from_9728 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 163987 (List.range' 9728 4857) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 163987 165523 178558 9728 512 4345 n2s_block_9728 n2s_from_10240
theorem n2s_from_9216 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 162451 (List.range' 9216 5369) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 162451 163987 178558 9216 512 4857 n2s_block_9216 n2s_from_9728
theorem n2s_from_8704 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 160915 (List.range' 8704 5881) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 160915 162451 178558 8704 512 5369 n2s_block_8704 n2s_from_9216
theorem n2s_from_8192 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 159379 (List.range' 8192 6393) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 159379 160915 178558 8192 512 5881 n2s_block_8192 n2s_from_8704
theorem n2s_from_7680 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 157843 (List.range' 7680 6905) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 157843 159379 178558 7680 512 6393 n2s_block_7680 n2s_from_8192
theorem n2s_from_7168 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 156307 (List.range' 7168 7417) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 156307 157843 178558 7168 512 6905 n2s_block_7168 n2s_from_7680
theorem n2s_from_6656 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 154771 (List.range' 6656 7929) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 154771 156307 178558 6656 512 7417 n2s_block_6656 n2s_from_7168
theorem n2s_from_6144 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 153235 (List.range' 6144 8441) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 153235 154771 178558 6144 512 7929 n2s_block_6144 n2s_from_6656
theorem n2s_from_5632 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 151699 (List.range' 5632 8953) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 151699 153235 178558 5632 512 8441 n2s_block_5632 n2s_from_6144
theorem n2s_from_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 150163 (List.range' 5120 9465) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 150163 151699 178558 5120 512 8953 n2s_block_5120 n2s_from_5632
theorem n2s_from_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 148627 (List.range' 4608 9977) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 148627 150163 178558 4608 512 9465 n2s_block_4608 n2s_from_5120
theorem n2s_from_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 147091 (List.range' 4096 10489) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 147091 148627 178558 4096 512 9977 n2s_block_4096 n2s_from_4608
theorem n2s_from_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 145555 (List.range' 3584 11001) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 145555 147091 178558 3584 512 10489 n2s_block_3584 n2s_from_4096
theorem n2s_from_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 144019 (List.range' 3072 11513) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 144019 145555 178558 3072 512 11001 n2s_block_3072 n2s_from_3584
theorem n2s_from_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 142483 (List.range' 2560 12025) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 142483 144019 178558 2560 512 11513 n2s_block_2560 n2s_from_3072
theorem n2s_from_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 140947 (List.range' 2048 12537) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 140947 142483 178558 2048 512 12025 n2s_block_2048 n2s_from_2560
theorem n2s_from_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 139411 (List.range' 1536 13049) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 139411 140947 178558 1536 512 12537 n2s_block_1536 n2s_from_2048
theorem n2s_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 137875 (List.range' 1024 13561) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 137875 139411 178558 1024 512 13049 n2s_block_1024 n2s_from_1536
theorem n2s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 136339 (List.range' 512 14073) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 136339 137875 178558 512 512 13561 n2s_block_512 n2s_from_1024
theorem n2s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 134803 (List.range' 0 14585) = some 178558 :=
  walk_range_join (fun p => nodeWords (p % 5)) 134803 136339 178558 0 512 14073 n2s_block_0 n2s_from_512
theorem n2r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 178560 (List.range' 0 179) = some 179097 :=
  n2r_block_0
theorem n3s_from_7680 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 202150 (List.range' 7680 215) = some 202795 :=
  n3s_block_7680
theorem n3s_from_7168 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 200614 (List.range' 7168 727) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 200614 202150 202795 7168 512 215 n3s_block_7168 n3s_from_7680
theorem n3s_from_6656 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 199078 (List.range' 6656 1239) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 199078 200614 202795 6656 512 727 n3s_block_6656 n3s_from_7168
theorem n3s_from_6144 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 197542 (List.range' 6144 1751) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 197542 199078 202795 6144 512 1239 n3s_block_6144 n3s_from_6656
theorem n3s_from_5632 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 196006 (List.range' 5632 2263) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 196006 197542 202795 5632 512 1751 n3s_block_5632 n3s_from_6144
theorem n3s_from_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 194470 (List.range' 5120 2775) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 194470 196006 202795 5120 512 2263 n3s_block_5120 n3s_from_5632
theorem n3s_from_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 192934 (List.range' 4608 3287) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 192934 194470 202795 4608 512 2775 n3s_block_4608 n3s_from_5120
theorem n3s_from_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 191398 (List.range' 4096 3799) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 191398 192934 202795 4096 512 3287 n3s_block_4096 n3s_from_4608
theorem n3s_from_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 189862 (List.range' 3584 4311) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 189862 191398 202795 3584 512 3799 n3s_block_3584 n3s_from_4096
theorem n3s_from_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 188326 (List.range' 3072 4823) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 188326 189862 202795 3072 512 4311 n3s_block_3072 n3s_from_3584
theorem n3s_from_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 186790 (List.range' 2560 5335) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 186790 188326 202795 2560 512 4823 n3s_block_2560 n3s_from_3072
theorem n3s_from_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 185254 (List.range' 2048 5847) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 185254 186790 202795 2048 512 5335 n3s_block_2048 n3s_from_2560
theorem n3s_from_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 183718 (List.range' 1536 6359) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 183718 185254 202795 1536 512 5847 n3s_block_1536 n3s_from_2048
theorem n3s_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 182182 (List.range' 1024 6871) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 182182 183718 202795 1024 512 6359 n3s_block_1024 n3s_from_1536
theorem n3s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 180646 (List.range' 512 7383) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 180646 182182 202795 512 512 6871 n3s_block_512 n3s_from_1024
theorem n3s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 179110 (List.range' 0 7895) = some 202795 :=
  walk_range_join (fun p => nodeWords (p % 5)) 179110 180646 202795 0 512 7383 n3s_block_0 n3s_from_512
theorem n3r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 202797 (List.range' 0 3) = some 202806 :=
  n3r_block_0
theorem n4s_from_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 215111 (List.range' 4096 374) = some 216233 :=
  n4s_block_4096
theorem n4s_from_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 213575 (List.range' 3584 886) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 213575 215111 216233 3584 512 374 n4s_block_3584 n4s_from_4096
theorem n4s_from_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 212039 (List.range' 3072 1398) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 212039 213575 216233 3072 512 886 n4s_block_3072 n4s_from_3584
theorem n4s_from_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 210503 (List.range' 2560 1910) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 210503 212039 216233 2560 512 1398 n4s_block_2560 n4s_from_3072
theorem n4s_from_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 208967 (List.range' 2048 2422) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 208967 210503 216233 2048 512 1910 n4s_block_2048 n4s_from_2560
theorem n4s_from_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 207431 (List.range' 1536 2934) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 207431 208967 216233 1536 512 2422 n4s_block_1536 n4s_from_2048
theorem n4s_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 205895 (List.range' 1024 3446) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 205895 207431 216233 1024 512 2934 n4s_block_1024 n4s_from_1536
theorem n4s_from_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 204359 (List.range' 512 3958) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 204359 205895 216233 512 512 3446 n4s_block_512 n4s_from_1024
theorem n4s_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 202823 (List.range' 0 4470) = some 216233 :=
  walk_range_join (fun p => nodeWords (p % 5)) 202823 204359 216233 0 512 3958 n4s_block_0 n4s_from_512
theorem n4r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 216235 (List.range' 0 24) = some 216307 :=
  n4r_block_0
theorem n5r_from_5120 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 231680 (List.range' 5120 249) = some 232427 :=
  n5r_block_5120
theorem n5r_from_4608 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 230144 (List.range' 4608 761) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 230144 231680 232427 4608 512 249 n5r_block_4608 n5r_from_5120
theorem n5r_from_4096 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 228608 (List.range' 4096 1273) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 228608 230144 232427 4096 512 761 n5r_block_4096 n5r_from_4608
theorem n5r_from_3584 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 227072 (List.range' 3584 1785) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 227072 228608 232427 3584 512 1273 n5r_block_3584 n5r_from_4096
theorem n5r_from_3072 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 225536 (List.range' 3072 2297) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 225536 227072 232427 3072 512 1785 n5r_block_3072 n5r_from_3584
theorem n5r_from_2560 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 224000 (List.range' 2560 2809) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 224000 225536 232427 2560 512 2297 n5r_block_2560 n5r_from_3072
theorem n5r_from_2048 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 222464 (List.range' 2048 3321) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 222464 224000 232427 2048 512 2809 n5r_block_2048 n5r_from_2560
theorem n5r_from_1536 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 220928 (List.range' 1536 3833) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 220928 222464 232427 1536 512 3321 n5r_block_1536 n5r_from_2048
theorem n5r_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 219392 (List.range' 1024 4345) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 219392 220928 232427 1024 512 3833 n5r_block_1024 n5r_from_1536
theorem n5r_from_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 217856 (List.range' 512 4857) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 217856 219392 232427 512 512 4345 n5r_block_512 n5r_from_1024
theorem n5r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 216320 (List.range' 0 5369) = some 232427 :=
  walk_range_join (fun p => nodeWords (p % 5)) 216320 217856 232427 0 512 4857 n5r_block_0 n5r_from_512
theorem n6r_from_1024 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 235512 (List.range' 1024 50) = some 235662 :=
  n6r_block_1024
theorem n6r_from_512 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 233976 (List.range' 512 562) = some 235662 :=
  walk_range_join (fun p => nodeWords (p % 5)) 233976 235512 235662 512 512 50 n6r_block_512 n6r_from_1024
theorem n6r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 232440 (List.range' 0 1074) = some 235662 :=
  walk_range_join (fun p => nodeWords (p % 5)) 232440 233976 235662 0 512 562 n6r_block_0 n6r_from_512
theorem n7r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 235675 (List.range' 0 215) = some 236320 :=
  n7r_block_0
theorem n8r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 236329 (List.range' 0 43) = some 236458 :=
  n8r_block_0
theorem n9r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 236475 (List.range' 0 9) = some 236502 :=
  n9r_block_0
theorem n10r_from_0 : walk 32 Artifact.commitCode (fun p => nodeWords (p % 5)) 236515 (List.range' 0 2) = some 236521 :=
  n10r_block_0

theorem seg_0 : walk 32 Artifact.commitCode id 0 [setupWords] = some 19 := by decide +kernel
theorem seg_1 : walk 32 Artifact.commitCode id 19 [leafCode] = some 45183 := by
  rw [show leafCode = (List.range' 0 4096).flatMap leafWords by rw [leafCode, List.range_eq_range']]
  exact walk_flatten 32 _ leafWords _ 19 45183 leaf_from_0
theorem seg_2 : walk 32 Artifact.commitCode id 45183 [leafLatchWords] = some 45201 := by decide +kernel
theorem seg_3 : walk 32 Artifact.commitCode id 45201 [leafZeroWords] = some 45217 := by decide +kernel
theorem seg_4 : walk 32 Artifact.commitCode id 45217 [levelSetupWords 1] = some 45226 := by decide +kernel
theorem seg_5 : walk 32 Artifact.commitCode id 45226 [nodeCode (levelS 1)] = some 133516 := by
  rw [show nodeCode (levelS 1) = (List.range' 0 29430).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelS 1 = 29430 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 45226 133516 n1s_from_0
theorem seg_6 : walk 32 Artifact.commitCode id 133516 [levelLatchWords 1] = some 133518 := by decide +kernel
theorem seg_7 : walk 32 Artifact.commitCode id 133518 [nodeCode (levelR 1)] = some 134790 := by
  rw [show nodeCode (levelR 1) = (List.range' 0 424).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 1 = 424 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 133518 134790 n1r_from_0
theorem seg_8 : walk 32 Artifact.commitCode id 134790 [levelZeroWords 1] = some 134794 := by decide +kernel
theorem seg_9 : walk 32 Artifact.commitCode id 134794 [levelSetupWords 2] = some 134803 := by decide +kernel
theorem seg_10 : walk 32 Artifact.commitCode id 134803 [nodeCode (levelS 2)] = some 178558 := by
  rw [show nodeCode (levelS 2) = (List.range' 0 14585).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelS 2 = 14585 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 134803 178558 n2s_from_0
theorem seg_11 : walk 32 Artifact.commitCode id 178558 [levelLatchWords 2] = some 178560 := by decide +kernel
theorem seg_12 : walk 32 Artifact.commitCode id 178560 [nodeCode (levelR 2)] = some 179097 := by
  rw [show nodeCode (levelR 2) = (List.range' 0 179).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 2 = 179 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 178560 179097 n2r_from_0
theorem seg_13 : walk 32 Artifact.commitCode id 179097 [levelZeroWords 2] = some 179101 := by decide +kernel
theorem seg_14 : walk 32 Artifact.commitCode id 179101 [levelSetupWords 3] = some 179110 := by decide +kernel
theorem seg_15 : walk 32 Artifact.commitCode id 179110 [nodeCode (levelS 3)] = some 202795 := by
  rw [show nodeCode (levelS 3) = (List.range' 0 7895).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelS 3 = 7895 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 179110 202795 n3s_from_0
theorem seg_16 : walk 32 Artifact.commitCode id 202795 [levelLatchWords 3] = some 202797 := by decide +kernel
theorem seg_17 : walk 32 Artifact.commitCode id 202797 [nodeCode (levelR 3)] = some 202806 := by
  rw [show nodeCode (levelR 3) = (List.range' 0 3).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 3 = 3 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 202797 202806 n3r_from_0
theorem seg_18 : walk 32 Artifact.commitCode id 202806 [levelZeroWords 3] = some 202814 := by decide +kernel
theorem seg_19 : walk 32 Artifact.commitCode id 202814 [levelSetupWords 4] = some 202823 := by decide +kernel
theorem seg_20 : walk 32 Artifact.commitCode id 202823 [nodeCode (levelS 4)] = some 216233 := by
  rw [show nodeCode (levelS 4) = (List.range' 0 4470).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelS 4 = 4470 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 202823 216233 n4s_from_0
theorem seg_21 : walk 32 Artifact.commitCode id 216233 [levelLatchWords 4] = some 216235 := by decide +kernel
theorem seg_22 : walk 32 Artifact.commitCode id 216235 [nodeCode (levelR 4)] = some 216307 := by
  rw [show nodeCode (levelR 4) = (List.range' 0 24).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 4 = 24 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 216235 216307 n4r_from_0
theorem seg_23 : walk 32 Artifact.commitCode id 216307 [levelZeroWords 4] = some 216311 := by decide +kernel
theorem seg_24 : walk 32 Artifact.commitCode id 216311 [levelSetupWords 5] = some 216320 := by decide +kernel
theorem seg_25 : walk 32 Artifact.commitCode id 216320 [nodeCode (levelR 5)] = some 232427 := by
  rw [show nodeCode (levelR 5) = (List.range' 0 5369).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 5 = 5369 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 216320 232427 n5r_from_0
theorem seg_26 : walk 32 Artifact.commitCode id 232427 [levelZeroWords 5] = some 232431 := by decide +kernel
theorem seg_27 : walk 32 Artifact.commitCode id 232431 [levelSetupWords 6] = some 232440 := by decide +kernel
theorem seg_28 : walk 32 Artifact.commitCode id 232440 [nodeCode (levelR 6)] = some 235662 := by
  rw [show nodeCode (levelR 6) = (List.range' 0 1074).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 6 = 1074 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 232440 235662 n6r_from_0
theorem seg_29 : walk 32 Artifact.commitCode id 235662 [levelZeroWords 6] = some 235666 := by decide +kernel
theorem seg_30 : walk 32 Artifact.commitCode id 235666 [levelSetupWords 7] = some 235675 := by decide +kernel
theorem seg_31 : walk 32 Artifact.commitCode id 235675 [nodeCode (levelR 7)] = some 236320 := by
  rw [show nodeCode (levelR 7) = (List.range' 0 215).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 7 = 215 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 235675 236320 n7r_from_0
theorem seg_32 : walk 32 Artifact.commitCode id 236320 [levelZeroWords 7] = some 236320 := by decide +kernel
theorem seg_33 : walk 32 Artifact.commitCode id 236320 [levelSetupWords 8] = some 236329 := by decide +kernel
theorem seg_34 : walk 32 Artifact.commitCode id 236329 [nodeCode (levelR 8)] = some 236458 := by
  rw [show nodeCode (levelR 8) = (List.range' 0 43).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 8 = 43 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 236329 236458 n8r_from_0
theorem seg_35 : walk 32 Artifact.commitCode id 236458 [levelZeroWords 8] = some 236466 := by decide +kernel
theorem seg_36 : walk 32 Artifact.commitCode id 236466 [levelSetupWords 9] = some 236475 := by decide +kernel
theorem seg_37 : walk 32 Artifact.commitCode id 236475 [nodeCode (levelR 9)] = some 236502 := by
  rw [show nodeCode (levelR 9) = (List.range' 0 9).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 9 = 9 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 236475 236502 n9r_from_0
theorem seg_38 : walk 32 Artifact.commitCode id 236502 [levelZeroWords 9] = some 236506 := by decide +kernel
theorem seg_39 : walk 32 Artifact.commitCode id 236506 [levelSetupWords 10] = some 236515 := by decide +kernel
theorem seg_40 : walk 32 Artifact.commitCode id 236515 [nodeCode (levelR 10)] = some 236521 := by
  rw [show nodeCode (levelR 10) = (List.range' 0 2).flatMap (fun p => nodeWords (p % 5)) by
    rw [show levelR 10 = 2 from rfl, nodeCode, List.range_eq_range']]
  exact walk_flatten 32 _ _ _ 236515 236521 n10r_from_0
theorem seg_41 : walk 32 Artifact.commitCode id 236521 [levelZeroWords 10] = some 236533 := by decide +kernel
theorem seg_42 : walk 32 Artifact.commitCode id 236533 [rootSetupWords] = some 236538 := by decide +kernel
theorem seg_43 : walk 32 Artifact.commitCode id 236538 [rootWords] = some 237421 := by decide +kernel

theorem tail_43 : walk 32 Artifact.commitCode id 236538 [rootWords] = some 237421 := seg_43
theorem tail_42 : walk 32 Artifact.commitCode id 236533 ([rootSetupWords] ++ [rootWords]) = some 237421 :=
  walk_append 32 _ id _ _ 236533 236538 237421 seg_42 tail_43
theorem tail_41 : walk 32 Artifact.commitCode id 236521 ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])) = some 237421 :=
  walk_append 32 _ id _ _ 236521 236533 237421 seg_41 tail_42
theorem tail_40 : walk 32 Artifact.commitCode id 236515 ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))) = some 237421 :=
  walk_append 32 _ id _ _ 236515 236521 237421 seg_40 tail_41
theorem tail_39 : walk 32 Artifact.commitCode id 236506 ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))) = some 237421 :=
  walk_append 32 _ id _ _ 236506 236515 237421 seg_39 tail_40
theorem tail_38 : walk 32 Artifact.commitCode id 236502 ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))) = some 237421 :=
  walk_append 32 _ id _ _ 236502 236506 237421 seg_38 tail_39
theorem tail_37 : walk 32 Artifact.commitCode id 236475 ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))) = some 237421 :=
  walk_append 32 _ id _ _ 236475 236502 237421 seg_37 tail_38
theorem tail_36 : walk 32 Artifact.commitCode id 236466 ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))) = some 237421 :=
  walk_append 32 _ id _ _ 236466 236475 237421 seg_36 tail_37
theorem tail_35 : walk 32 Artifact.commitCode id 236458 ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))) = some 237421 :=
  walk_append 32 _ id _ _ 236458 236466 237421 seg_35 tail_36
theorem tail_34 : walk 32 Artifact.commitCode id 236329 ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 236329 236458 237421 seg_34 tail_35
theorem tail_33 : walk 32 Artifact.commitCode id 236320 ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 236320 236329 237421 seg_33 tail_34
theorem tail_32 : walk 32 Artifact.commitCode id 236320 ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 236320 236320 237421 seg_32 tail_33
theorem tail_31 : walk 32 Artifact.commitCode id 235675 ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 235675 236320 237421 seg_31 tail_32
theorem tail_30 : walk 32 Artifact.commitCode id 235666 ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 235666 235675 237421 seg_30 tail_31
theorem tail_29 : walk 32 Artifact.commitCode id 235662 ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 235662 235666 237421 seg_29 tail_30
theorem tail_28 : walk 32 Artifact.commitCode id 232440 ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 232440 235662 237421 seg_28 tail_29
theorem tail_27 : walk 32 Artifact.commitCode id 232431 ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 232431 232440 237421 seg_27 tail_28
theorem tail_26 : walk 32 Artifact.commitCode id 232427 ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 232427 232431 237421 seg_26 tail_27
theorem tail_25 : walk 32 Artifact.commitCode id 216320 ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 216320 232427 237421 seg_25 tail_26
theorem tail_24 : walk 32 Artifact.commitCode id 216311 ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 216311 216320 237421 seg_24 tail_25
theorem tail_23 : walk 32 Artifact.commitCode id 216307 ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 216307 216311 237421 seg_23 tail_24
theorem tail_22 : walk 32 Artifact.commitCode id 216235 ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 216235 216307 237421 seg_22 tail_23
theorem tail_21 : walk 32 Artifact.commitCode id 216233 ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 216233 216235 237421 seg_21 tail_22
theorem tail_20 : walk 32 Artifact.commitCode id 202823 ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 202823 216233 237421 seg_20 tail_21
theorem tail_19 : walk 32 Artifact.commitCode id 202814 ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 202814 202823 237421 seg_19 tail_20
theorem tail_18 : walk 32 Artifact.commitCode id 202806 ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 202806 202814 237421 seg_18 tail_19
theorem tail_17 : walk 32 Artifact.commitCode id 202797 ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 202797 202806 237421 seg_17 tail_18
theorem tail_16 : walk 32 Artifact.commitCode id 202795 ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 202795 202797 237421 seg_16 tail_17
theorem tail_15 : walk 32 Artifact.commitCode id 179110 ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 179110 202795 237421 seg_15 tail_16
theorem tail_14 : walk 32 Artifact.commitCode id 179101 ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 179101 179110 237421 seg_14 tail_15
theorem tail_13 : walk 32 Artifact.commitCode id 179097 ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 179097 179101 237421 seg_13 tail_14
theorem tail_12 : walk 32 Artifact.commitCode id 178560 ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 178560 179097 237421 seg_12 tail_13
theorem tail_11 : walk 32 Artifact.commitCode id 178558 ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 178558 178560 237421 seg_11 tail_12
theorem tail_10 : walk 32 Artifact.commitCode id 134803 ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 134803 178558 237421 seg_10 tail_11
theorem tail_9 : walk 32 Artifact.commitCode id 134794 ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 134794 134803 237421 seg_9 tail_10
theorem tail_8 : walk 32 Artifact.commitCode id 134790 ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 134790 134794 237421 seg_8 tail_9
theorem tail_7 : walk 32 Artifact.commitCode id 133518 ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 133518 134790 237421 seg_7 tail_8
theorem tail_6 : walk 32 Artifact.commitCode id 133516 ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 133516 133518 237421 seg_6 tail_7
theorem tail_5 : walk 32 Artifact.commitCode id 45226 ([nodeCode (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 45226 133516 237421 seg_5 tail_6
theorem tail_4 : walk 32 Artifact.commitCode id 45217 ([levelSetupWords 1] ++ ([nodeCode (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 45217 45226 237421 seg_4 tail_5
theorem tail_3 : walk 32 Artifact.commitCode id 45201 ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCode (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 45201 45217 237421 seg_3 tail_4
theorem tail_2 : walk 32 Artifact.commitCode id 45183 ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCode (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 45183 45201 237421 seg_2 tail_3
theorem tail_1 : walk 32 Artifact.commitCode id 19 ([leafCode] ++ ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCode (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 19 45183 237421 seg_1 tail_2
theorem tail_0 : walk 32 Artifact.commitCode id 0 ([setupWords] ++ ([leafCode] ++ ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCode (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords]))))))))))))))))))))))))))))))))))))))))))) = some 237421 :=
  walk_append 32 _ id _ _ 0 19 237421 seg_0 tail_1
theorem level_code_1 : levelCode 1 = levelSetupWords 1 ++ (nodeCode (levelS 1) ++
    (levelLatchWords 1 ++ (nodeCode (levelR 1) ++ levelZeroWords 1))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc]
theorem level_code_2 : levelCode 2 = levelSetupWords 2 ++ (nodeCode (levelS 2) ++
    (levelLatchWords 2 ++ (nodeCode (levelR 2) ++ levelZeroWords 2))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc]
theorem level_code_3 : levelCode 3 = levelSetupWords 3 ++ (nodeCode (levelS 3) ++
    (levelLatchWords 3 ++ (nodeCode (levelR 3) ++ levelZeroWords 3))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc]
theorem level_code_4 : levelCode 4 = levelSetupWords 4 ++ (nodeCode (levelS 4) ++
    (levelLatchWords 4 ++ (nodeCode (levelR 4) ++ levelZeroWords 4))) := by
  rw [levelCode, if_neg (by decide)]
  simp only [List.append_assoc]
theorem level_code_5 : levelCode 5 = levelSetupWords 5 ++ (nodeCode (levelR 5) ++ levelZeroWords 5) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc]
theorem level_code_6 : levelCode 6 = levelSetupWords 6 ++ (nodeCode (levelR 6) ++ levelZeroWords 6) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc]
theorem level_code_7 : levelCode 7 = levelSetupWords 7 ++ (nodeCode (levelR 7) ++ levelZeroWords 7) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc]
theorem level_code_8 : levelCode 8 = levelSetupWords 8 ++ (nodeCode (levelR 8) ++ levelZeroWords 8) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc]
theorem level_code_9 : levelCode 9 = levelSetupWords 9 ++ (nodeCode (levelR 9) ++ levelZeroWords 9) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc]
theorem level_code_10 : levelCode 10 = levelSetupWords 10 ++ (nodeCode (levelR 10) ++ levelZeroWords 10) := by
  rw [levelCode, if_pos (by decide)]
  simp only [List.nil_append, List.append_assoc]

theorem commit_code_matches : matchesFrom 32 Artifact.commitCode 0 image.code = true := by
  obtain ⟨ok, len⟩ := walk_sound 32 _ id _ 0 237421 tail_0
  have code : image.code = (([setupWords] ++ ([leafCode] ++ ([leafLatchWords] ++ ([leafZeroWords] ++ ([levelSetupWords 1] ++ ([nodeCode (levelS 1)] ++ ([levelLatchWords 1] ++ ([nodeCode (levelR 1)] ++ ([levelZeroWords 1] ++ ([levelSetupWords 2] ++ ([nodeCode (levelS 2)] ++ ([levelLatchWords 2] ++ ([nodeCode (levelR 2)] ++ ([levelZeroWords 2] ++ ([levelSetupWords 3] ++ ([nodeCode (levelS 3)] ++ ([levelLatchWords 3] ++ ([nodeCode (levelR 3)] ++ ([levelZeroWords 3] ++ ([levelSetupWords 4] ++ ([nodeCode (levelS 4)] ++ ([levelLatchWords 4] ++ ([nodeCode (levelR 4)] ++ ([levelZeroWords 4] ++ ([levelSetupWords 5] ++ ([nodeCode (levelR 5)] ++ ([levelZeroWords 5] ++ ([levelSetupWords 6] ++ ([nodeCode (levelR 6)] ++ ([levelZeroWords 6] ++ ([levelSetupWords 7] ++ ([nodeCode (levelR 7)] ++ ([levelZeroWords 7] ++ ([levelSetupWords 8] ++ ([nodeCode (levelR 8)] ++ ([levelZeroWords 8] ++ ([levelSetupWords 9] ++ ([nodeCode (levelR 9)] ++ ([levelZeroWords 9] ++ ([levelSetupWords 10] ++ ([nodeCode (levelR 10)] ++ ([levelZeroWords 10] ++ ([rootSetupWords] ++ [rootWords])))))))))))))))))))))))))))))))))))))))))))).flatMap id := by
    simp only [image, levelsCode, level_code_1, level_code_2, level_code_3, level_code_4, level_code_5, level_code_6, level_code_7, level_code_8, level_code_9, level_code_10,
      List.append_assoc, List.cons_append, List.nil_append, List.flatMap_cons, List.flatMap_nil, id, List.append_nil]
  rw [code]
  exact matches_of_prefix 32 _ _ 0 ok len

theorem quad_commit_image : Artifact.submission.image .commit = image := by
  simp only [Artifact.submission]
  rw [decode_of_matches 32 _ _ commit_code_matches]
  rfl

end TwoPermutationPrototype.ArtifactMatchB

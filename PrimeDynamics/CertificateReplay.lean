import PrimeDynamics.CertificateData
namespace PrimeDynamics.Certificate.Data
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def checkedCover (p : ℕ) : Bool :=
  if p ≤ 23333 then coverOK row 4096 p (witness p) else true
private theorem rows_0 : block (rowOK row) 0 6 = true := by decide +kernel
private theorem rows_64 : block (rowOK row) 64 6 = true := by decide +kernel
private theorem rows_128 : block (rowOK row) 128 6 = true := by decide +kernel
private theorem rows_192 : block (rowOK row) 192 6 = true := by decide +kernel
private theorem rows_256 : block (rowOK row) 256 6 = true := by decide +kernel
private theorem rows_320 : block (rowOK row) 320 6 = true := by decide +kernel
private theorem rows_384 : block (rowOK row) 384 6 = true := by decide +kernel
private theorem rows_448 : block (rowOK row) 448 6 = true := by decide +kernel
private theorem rows_512 : block (rowOK row) 512 6 = true := by decide +kernel
private theorem rows_576 : block (rowOK row) 576 6 = true := by decide +kernel
private theorem rows_640 : block (rowOK row) 640 6 = true := by decide +kernel
private theorem rows_704 : block (rowOK row) 704 6 = true := by decide +kernel
private theorem rows_768 : block (rowOK row) 768 6 = true := by decide +kernel
private theorem rows_832 : block (rowOK row) 832 6 = true := by decide +kernel
private theorem rows_896 : block (rowOK row) 896 6 = true := by decide +kernel
private theorem rows_960 : block (rowOK row) 960 6 = true := by decide +kernel
private theorem rows_1024 : block (rowOK row) 1024 6 = true := by decide +kernel
private theorem rows_1088 : block (rowOK row) 1088 6 = true := by decide +kernel
private theorem rows_1152 : block (rowOK row) 1152 6 = true := by decide +kernel
private theorem rows_1216 : block (rowOK row) 1216 6 = true := by decide +kernel
private theorem rows_1280 : block (rowOK row) 1280 6 = true := by decide +kernel
private theorem rows_1344 : block (rowOK row) 1344 6 = true := by decide +kernel
private theorem rows_1408 : block (rowOK row) 1408 6 = true := by decide +kernel
private theorem rows_1472 : block (rowOK row) 1472 6 = true := by decide +kernel
private theorem rows_1536 : block (rowOK row) 1536 6 = true := by decide +kernel
private theorem rows_1600 : block (rowOK row) 1600 6 = true := by decide +kernel
private theorem rows_1664 : block (rowOK row) 1664 6 = true := by decide +kernel
private theorem rows_1728 : block (rowOK row) 1728 6 = true := by decide +kernel
private theorem rows_1792 : block (rowOK row) 1792 6 = true := by decide +kernel
private theorem rows_1856 : block (rowOK row) 1856 6 = true := by decide +kernel
private theorem rows_1920 : block (rowOK row) 1920 6 = true := by decide +kernel
private theorem rows_1984 : block (rowOK row) 1984 6 = true := by decide +kernel
private theorem rows_2048 : block (rowOK row) 2048 6 = true := by decide +kernel
private theorem rows_2112 : block (rowOK row) 2112 6 = true := by decide +kernel
private theorem rows_2176 : block (rowOK row) 2176 6 = true := by decide +kernel
private theorem rows_2240 : block (rowOK row) 2240 6 = true := by decide +kernel
private theorem rows_2304 : block (rowOK row) 2304 6 = true := by decide +kernel
private theorem rows_2368 : block (rowOK row) 2368 6 = true := by decide +kernel
private theorem rows_2432 : block (rowOK row) 2432 6 = true := by decide +kernel
private theorem rows_2496 : block (rowOK row) 2496 6 = true := by decide +kernel
private theorem rows_2560 : block (rowOK row) 2560 6 = true := by decide +kernel
private theorem rows_2624 : block (rowOK row) 2624 6 = true := by decide +kernel
private theorem rows_2688 : block (rowOK row) 2688 6 = true := by decide +kernel
private theorem rows_2752 : block (rowOK row) 2752 6 = true := by decide +kernel
private theorem rows_2816 : block (rowOK row) 2816 6 = true := by decide +kernel
private theorem rows_2880 : block (rowOK row) 2880 6 = true := by decide +kernel
private theorem rows_2944 : block (rowOK row) 2944 6 = true := by decide +kernel
private theorem rows_3008 : block (rowOK row) 3008 6 = true := by decide +kernel
private theorem rows_3072 : block (rowOK row) 3072 6 = true := by decide +kernel
private theorem rows_3136 : block (rowOK row) 3136 6 = true := by decide +kernel
private theorem rows_3200 : block (rowOK row) 3200 6 = true := by decide +kernel
private theorem rows_3264 : block (rowOK row) 3264 6 = true := by decide +kernel
private theorem rows_3328 : block (rowOK row) 3328 6 = true := by decide +kernel
private theorem rows_3392 : block (rowOK row) 3392 6 = true := by decide +kernel
private theorem rows_3456 : block (rowOK row) 3456 6 = true := by decide +kernel
private theorem rows_3520 : block (rowOK row) 3520 6 = true := by decide +kernel
private theorem rows_3584 : block (rowOK row) 3584 6 = true := by decide +kernel
private theorem rows_3648 : block (rowOK row) 3648 6 = true := by decide +kernel
private theorem rows_3712 : block (rowOK row) 3712 6 = true := by decide +kernel
private theorem rows_3776 : block (rowOK row) 3776 6 = true := by decide +kernel
private theorem rows_3840 : block (rowOK row) 3840 6 = true := by decide +kernel
private theorem rows_3904 : block (rowOK row) 3904 6 = true := by decide +kernel
private theorem rows_3968 : block (rowOK row) 3968 6 = true := by decide +kernel
private theorem rows_4032 : block (rowOK row) 4032 6 = true := by decide +kernel
theorem rows_checked : block (rowOK row) 0 12 = true :=
  (block_join (block_join (block_join (block_join (block_join (block_join rows_0 rows_64) (block_join rows_128 rows_192)) (block_join (block_join rows_256 rows_320) (block_join rows_384 rows_448))) (block_join (block_join (block_join rows_512 rows_576) (block_join rows_640 rows_704)) (block_join (block_join rows_768 rows_832) (block_join rows_896 rows_960)))) (block_join (block_join (block_join (block_join rows_1024 rows_1088) (block_join rows_1152 rows_1216)) (block_join (block_join rows_1280 rows_1344) (block_join rows_1408 rows_1472))) (block_join (block_join (block_join rows_1536 rows_1600) (block_join rows_1664 rows_1728)) (block_join (block_join rows_1792 rows_1856) (block_join rows_1920 rows_1984))))) (block_join (block_join (block_join (block_join (block_join rows_2048 rows_2112) (block_join rows_2176 rows_2240)) (block_join (block_join rows_2304 rows_2368) (block_join rows_2432 rows_2496))) (block_join (block_join (block_join rows_2560 rows_2624) (block_join rows_2688 rows_2752)) (block_join (block_join rows_2816 rows_2880) (block_join rows_2944 rows_3008)))) (block_join (block_join (block_join (block_join rows_3072 rows_3136) (block_join rows_3200 rows_3264)) (block_join (block_join rows_3328 rows_3392) (block_join rows_3456 rows_3520))) (block_join (block_join (block_join rows_3584 rows_3648) (block_join rows_3712 rows_3776)) (block_join (block_join rows_3840 rows_3904) (block_join rows_3968 rows_4032))))))

private theorem coverage_0 : block checkedCover 0 9 = true := by decide +kernel
private theorem coverage_512 : block checkedCover 512 9 = true := by decide +kernel
private theorem coverage_1024 : block checkedCover 1024 9 = true := by decide +kernel
private theorem coverage_1536 : block checkedCover 1536 9 = true := by decide +kernel
private theorem coverage_2048 : block checkedCover 2048 9 = true := by decide +kernel
private theorem coverage_2560 : block checkedCover 2560 9 = true := by decide +kernel
private theorem coverage_3072 : block checkedCover 3072 9 = true := by decide +kernel
private theorem coverage_3584 : block checkedCover 3584 9 = true := by decide +kernel
private theorem coverage_4096 : block checkedCover 4096 9 = true := by decide +kernel
private theorem coverage_4608 : block checkedCover 4608 9 = true := by decide +kernel
private theorem coverage_5120 : block checkedCover 5120 9 = true := by decide +kernel
private theorem coverage_5632 : block checkedCover 5632 9 = true := by decide +kernel
private theorem coverage_6144 : block checkedCover 6144 9 = true := by decide +kernel
private theorem coverage_6656 : block checkedCover 6656 9 = true := by decide +kernel
private theorem coverage_7168 : block checkedCover 7168 9 = true := by decide +kernel
private theorem coverage_7680 : block checkedCover 7680 9 = true := by decide +kernel
private theorem coverage_8192 : block checkedCover 8192 9 = true := by decide +kernel
private theorem coverage_8704 : block checkedCover 8704 9 = true := by decide +kernel
private theorem coverage_9216 : block checkedCover 9216 9 = true := by decide +kernel
private theorem coverage_9728 : block checkedCover 9728 9 = true := by decide +kernel
private theorem coverage_10240 : block checkedCover 10240 9 = true := by decide +kernel
private theorem coverage_10752 : block checkedCover 10752 9 = true := by decide +kernel
private theorem coverage_11264 : block checkedCover 11264 9 = true := by decide +kernel
private theorem coverage_11776 : block checkedCover 11776 9 = true := by decide +kernel
private theorem coverage_12288 : block checkedCover 12288 9 = true := by decide +kernel
private theorem coverage_12800 : block checkedCover 12800 9 = true := by decide +kernel
private theorem coverage_13312 : block checkedCover 13312 9 = true := by decide +kernel
private theorem coverage_13824 : block checkedCover 13824 9 = true := by decide +kernel
private theorem coverage_14336 : block checkedCover 14336 9 = true := by decide +kernel
private theorem coverage_14848 : block checkedCover 14848 9 = true := by decide +kernel
private theorem coverage_15360 : block checkedCover 15360 9 = true := by decide +kernel
private theorem coverage_15872 : block checkedCover 15872 9 = true := by decide +kernel
private theorem coverage_16384 : block checkedCover 16384 9 = true := by decide +kernel
private theorem coverage_16896 : block checkedCover 16896 9 = true := by decide +kernel
private theorem coverage_17408 : block checkedCover 17408 9 = true := by decide +kernel
private theorem coverage_17920 : block checkedCover 17920 9 = true := by decide +kernel
private theorem coverage_18432 : block checkedCover 18432 9 = true := by decide +kernel
private theorem coverage_18944 : block checkedCover 18944 9 = true := by decide +kernel
private theorem coverage_19456 : block checkedCover 19456 9 = true := by decide +kernel
private theorem coverage_19968 : block checkedCover 19968 9 = true := by decide +kernel
private theorem coverage_20480 : block checkedCover 20480 9 = true := by decide +kernel
private theorem coverage_20992 : block checkedCover 20992 9 = true := by decide +kernel
private theorem coverage_21504 : block checkedCover 21504 9 = true := by decide +kernel
private theorem coverage_22016 : block checkedCover 22016 9 = true := by decide +kernel
private theorem coverage_22528 : block checkedCover 22528 9 = true := by decide +kernel
private theorem coverage_23040 : block checkedCover 23040 9 = true := by decide +kernel
private theorem coverage_23552 : block checkedCover 23552 9 = true := by decide +kernel
private theorem coverage_24064 : block checkedCover 24064 9 = true := by decide +kernel
private theorem coverage_24576 : block checkedCover 24576 9 = true := by decide +kernel
private theorem coverage_25088 : block checkedCover 25088 9 = true := by decide +kernel
private theorem coverage_25600 : block checkedCover 25600 9 = true := by decide +kernel
private theorem coverage_26112 : block checkedCover 26112 9 = true := by decide +kernel
private theorem coverage_26624 : block checkedCover 26624 9 = true := by decide +kernel
private theorem coverage_27136 : block checkedCover 27136 9 = true := by decide +kernel
private theorem coverage_27648 : block checkedCover 27648 9 = true := by decide +kernel
private theorem coverage_28160 : block checkedCover 28160 9 = true := by decide +kernel
private theorem coverage_28672 : block checkedCover 28672 9 = true := by decide +kernel
private theorem coverage_29184 : block checkedCover 29184 9 = true := by decide +kernel
private theorem coverage_29696 : block checkedCover 29696 9 = true := by decide +kernel
private theorem coverage_30208 : block checkedCover 30208 9 = true := by decide +kernel
private theorem coverage_30720 : block checkedCover 30720 9 = true := by decide +kernel
private theorem coverage_31232 : block checkedCover 31232 9 = true := by decide +kernel
private theorem coverage_31744 : block checkedCover 31744 9 = true := by decide +kernel
private theorem coverage_32256 : block checkedCover 32256 9 = true := by decide +kernel
theorem coverage_checked : block checkedCover 0 15 = true :=
  (block_join (block_join (block_join (block_join (block_join (block_join coverage_0 coverage_512) (block_join coverage_1024 coverage_1536)) (block_join (block_join coverage_2048 coverage_2560) (block_join coverage_3072 coverage_3584))) (block_join (block_join (block_join coverage_4096 coverage_4608) (block_join coverage_5120 coverage_5632)) (block_join (block_join coverage_6144 coverage_6656) (block_join coverage_7168 coverage_7680)))) (block_join (block_join (block_join (block_join coverage_8192 coverage_8704) (block_join coverage_9216 coverage_9728)) (block_join (block_join coverage_10240 coverage_10752) (block_join coverage_11264 coverage_11776))) (block_join (block_join (block_join coverage_12288 coverage_12800) (block_join coverage_13312 coverage_13824)) (block_join (block_join coverage_14336 coverage_14848) (block_join coverage_15360 coverage_15872))))) (block_join (block_join (block_join (block_join (block_join coverage_16384 coverage_16896) (block_join coverage_17408 coverage_17920)) (block_join (block_join coverage_18432 coverage_18944) (block_join coverage_19456 coverage_19968))) (block_join (block_join (block_join coverage_20480 coverage_20992) (block_join coverage_21504 coverage_22016)) (block_join (block_join coverage_22528 coverage_23040) (block_join coverage_23552 coverage_24064)))) (block_join (block_join (block_join (block_join coverage_24576 coverage_25088) (block_join coverage_25600 coverage_26112)) (block_join (block_join coverage_26624 coverage_27136) (block_join coverage_27648 coverage_28160))) (block_join (block_join (block_join coverage_28672 coverage_29184) (block_join coverage_29696 coverage_30208)) (block_join (block_join coverage_30720 coverage_31232) (block_join coverage_31744 coverage_32256))))))

end PrimeDynamics.Certificate.Data


include "we.mm"
include "wM.mm"
include "wU.mm"
include "wI.mm"
include "ax.mm"
include "II.mm"
include "I_.mm"
include "III.mm"
include "IV.mm"

theorem theorem1

  assert |- M U I I U

  step 0) we(): wff 
  step 1) wM(0): wff M
  step 2) wU(1): wff M U
  step 3) wI(2): wff M U I
  step 4) we(): wff 
  step 5) wI(4): wff I
  step 6) wU(5): wff I U
  step 7) we(): wff 
  step 8) wU(7): wff U
  step 9) wI(8): wff U I
  step 10) wU(9): wff U I U
  step 11) we(): wff 
  step 12) wM(11): wff M
  step 13) we(): wff 
  step 14) wI(13): wff I
  step 15) wU(14): wff I U
  step 16) we(): wff 
  step 17) wM(16): wff M
  step 18) wI(17): wff M I
  step 19) wI(18): wff M I I
  step 20) wI(19): wff M I I I
  step 21) we(): wff 
  step 22) wI(21): wff I
  step 23) wI(22): wff I I
  step 24) we(): wff 
  step 25) wI(24): wff I
  step 26) ax(): |- M I
  step 27) II(25,26): |- M I I
  step 28) II(23,27): |- M I I I I
  step 29) I_(20,28): |- M I I I I U
  step 30) III(12,15,29): |- M U I U
  step 31) II(10,30): |- M U I U U I U
  step 32) IV(3,6,31): |- M U I I U
end

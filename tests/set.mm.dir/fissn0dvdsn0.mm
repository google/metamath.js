include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "wnel.mm"
include "w3a.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "fissn0dvds.mm"
include "rabn0.mm"
include "sylibr.mm"

theorem fissn0dvdsn0
  let vm: setvar m
  let vn: setvar n
  let cZ: class Z
  let vk: setvar k

  disjoint Z m
  disjoint Z n
  disjoint m n
  disjoint Z k
  disjoint k m
  disjoint k n
  assert |- ( ( Z C_ ZZ /\ Z e. Fin /\ 0 e/ Z ) -> { n e. NN | A. m e. Z m || n } =/= (/) )

  proof
    cZ
    cz
    wss
    cZ
    cfn
    wcel
    cc0
    cZ
    wnel
    w3a
    vm
    cv
    vn
    cv
    cdvds
    wbr
    vm
    cZ
    wral
    #
    vn
    cn
    wrex
    @0
    vn
    cn
    crab
    c0
    wne
    vm
    vn
    cZ
    fissn0dvds
    @0
    vn
    cn
    rabn0
    sylibr
end

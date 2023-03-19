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
include "crab.mm"
include "clcmf.mm"
include "cfv.mm"
include "ssrab2.mm"
include "lcmfcllem.mm"
include "sseldi.mm"

theorem lcmfn0cl
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  let vz: setvar z


  assert |- ( ( Z C_ ZZ /\ Z e. Fin /\ 0 e/ Z ) -> ( _lcm ` Z ) e. NN )

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
    crab
    cn
    cZ
    clcmf
    cfv
    @0
    vn
    cn
    ssrab2
    vm
    vn
    cZ
    lcmfcllem
    sseldi
end

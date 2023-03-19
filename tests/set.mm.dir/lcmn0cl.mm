include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "clcm.mm"
include "co.mm"
include "ssrab2.mm"
include "lcmcllem.mm"
include "sseldi.mm"

theorem lcmn0cl
  let cM: class M
  let cN: class N
  let cK: class K
  let vn: setvar n


  assert |- ( ( ( M e. ZZ /\ N e. ZZ ) /\ -. ( M = 0 \/ N = 0 ) ) -> ( M lcm N ) e. NN )

  proof
    cM
    cz
    wcel
    cN
    cz
    wcel
    wa
    cM
    cc0
    wceq
    cN
    cc0
    wceq
    wo
    wn
    wa
    cM
    vn
    cv
    #
    cdvds
    wbr
    cN
    @0
    cdvds
    wbr
    wa
    #
    vn
    cn
    crab
    cn
    cM
    cN
    clcm
    co
    @1
    vn
    cn
    ssrab2
    vn
    cM
    cN
    lcmcllem
    sseldi
end

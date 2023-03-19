include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cca.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cv.mm"
include "cuz.mm"
include "cbl.mm"
include "cres.mm"
include "wf.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "iscau.mm"
include "simprbda.mm"

theorem caufpm
  let cD: class D
  let cF: class F
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( D e. ( *Met ` X ) /\ F e. ( Cau ` D ) ) -> F e. ( X ^pm CC ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cF
    cD
    cca
    cfv
    wcel
    cF
    cX
    cc
    cpm
    co
    wcel
    vy
    cv
    #
    cuz
    cfv
    #
    @0
    cF
    cfv
    vx
    cv
    cD
    cbl
    cfv
    co
    cF
    @1
    cres
    wf
    vy
    cz
    wrex
    vx
    crp
    wral
    vx
    cD
    vy
    cF
    cX
    iscau
    simprbda
end

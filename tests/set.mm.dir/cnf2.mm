include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "iscn.mm"
include "simprbda.mm"
include "3impa.mm"

theorem cnf2
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ F e. ( J Cn K ) ) -> F : X --> Y )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    @0
    @1
    wa
    @2
    @3
    cF
    ccnv
    vx
    cv
    cima
    cJ
    wcel
    vx
    cK
    wral
    vx
    cF
    cJ
    cK
    cX
    cY
    iscn
    simprbda
    3impa
end

include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ctop.mm"
include "wa.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "eqid.mm"
include "iscn2.mm"
include "simplbi.mm"
include "simpld.mm"

theorem cntop1
  let cF: class F
  let cJ: class J
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  let cP: class P


  assert |- ( F e. ( J Cn K ) -> J e. Top )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    @0
    @1
    @2
    wa
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf
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
    wa
    vx
    cF
    cJ
    cK
    @3
    @4
    @3
    eqid
    @4
    eqid
    iscn2
    simplbi
    simpld
end

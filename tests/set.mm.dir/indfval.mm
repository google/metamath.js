include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cind.mm"
include "cfv.mm"
include "cr.mm"
include "cmpt.mm"
include "wceq.mm"
include "indval.mm"
include "3adant3.mm"
include "wa.mm"
include "simpr.mm"
include "eleq1d.mm"
include "ifbid.mm"
include "simp3.mm"
include "1re.mm"
include "0re.mm"
include "keepel.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem indfval
  let cA: class A
  let cO: class O
  let cV: class V
  let cX: class X
  let vx: setvar x


  assert |- ( ( O e. V /\ A C_ O /\ X e. O ) -> ( ( ( _Ind ` O ) ` A ) ` X ) = if ( X e. A , 1 , 0 ) )

  proof
    cO
    cV
    wcel
    #
    cA
    cO
    wss
    #
    cX
    cO
    wcel
    #
    w3a
    #
    vx
    cX
    vx
    cv
    #
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    cX
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    cO
    cA
    cO
    cind
    cfv
    cfv
    #
    cr
    @0
    @1
    @9
    vx
    cO
    @6
    cmpt
    wceq
    @2
    vx
    cA
    cO
    cV
    indval
    3adant3
    @3
    @4
    cX
    wceq
    #
    wa
    #
    @5
    @7
    c1
    cc0
    @11
    @4
    cX
    cA
    @3
    @10
    simpr
    eleq1d
    ifbid
    @0
    @1
    @2
    simp3
    @8
    cr
    wcel
    @3
    @7
    c1
    cc0
    cr
    1re
    0re
    keepel
    a1i
    fvmptd
end

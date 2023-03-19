include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cpw.mm"
include "cind.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "indv.mm"
include "adantr.mm"
include "eleq2.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "adantl.mm"
include "simpr.mm"
include "wb.mm"
include "ssexg.mm"
include "ancoms.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "mptexg.mm"
include "fvmptd.mm"

theorem indval
  let vx: setvar x
  let cA: class A
  let cO: class O
  let cV: class V
  let va: setvar a
  let vo: setvar o

  disjoint O x
  disjoint A x
  disjoint a o
  disjoint a x
  disjoint O a
  disjoint o x
  disjoint O o
  disjoint V a
  disjoint V o
  disjoint A a
  assert |- ( ( O e. V /\ A C_ O ) -> ( ( _Ind ` O ) ` A ) = ( x e. O |-> if ( x e. A , 1 , 0 ) ) )

  proof
    cO
    cV
    wcel
    #
    cA
    cO
    wss
    #
    wa
    #
    va
    cA
    vx
    cO
    vx
    cv
    #
    va
    cv
    #
    wcel
    #
    c1
    cc0
    cif
    #
    cmpt
    #
    vx
    cO
    @3
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    cmpt
    #
    cO
    cpw
    #
    cO
    cind
    cfv
    #
    cvv
    @0
    @12
    va
    @11
    @7
    cmpt
    wceq
    @1
    vx
    cO
    cV
    va
    indv
    adantr
    @4
    cA
    wceq
    #
    @7
    @10
    wceq
    @2
    @13
    vx
    cO
    @6
    @9
    @13
    @5
    @8
    c1
    cc0
    @4
    cA
    @3
    eleq2
    ifbid
    mpteq2dv
    adantl
    @2
    cA
    @11
    wcel
    #
    @1
    @0
    @1
    simpr
    @2
    cA
    cvv
    wcel
    #
    @14
    @1
    wb
    @1
    @0
    @15
    cA
    cO
    cV
    ssexg
    ancoms
    cA
    cO
    cvv
    elpwg
    syl
    mpbird
    @0
    @10
    cvv
    wcel
    @1
    vx
    cO
    @9
    cV
    mptexg
    adantr
    fvmptd
end

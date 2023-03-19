include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "copab.mm"
include "wss.mm"
include "fssxp.mm"
include "df-ss.mm"
include "sylib.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn5.mm"
include "ineq1d.mm"
include "eqtr3d.mm"
include "df-mpt.mm"
include "df-xp.mm"
include "ineq12i.mm"
include "inopab.mm"
include "anandi.mm"
include "ancom.mm"
include "anbi2i.mm"
include "anass.mm"
include "eqcom.mm"
include "3bitr2i.mm"
include "bitr3i.mm"
include "opabbii.mm"
include "3eqtri.mm"
include "syl6eq.mm"

theorem fgraphopab
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vx: setvar x

  disjoint F a
  disjoint F b
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint F x
  disjoint a x
  disjoint b x
  disjoint A x
  disjoint B x
  assert |- ( F : A --> B -> F = { <. a , b >. | ( ( a e. A /\ b e. B ) /\ ( F ` a ) = b ) } )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    va
    cA
    va
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cA
    cB
    cxp
    #
    cin
    #
    @1
    cA
    wcel
    #
    vb
    cv
    #
    cB
    wcel
    #
    wa
    #
    @2
    @7
    wceq
    #
    wa
    #
    va
    vb
    copab
    #
    @0
    cF
    @4
    cin
    #
    cF
    @5
    @0
    cF
    @4
    wss
    @13
    cF
    wceq
    cA
    cB
    cF
    fssxp
    cF
    @4
    df-ss
    sylib
    @0
    cF
    @3
    @4
    @0
    cF
    cA
    wfn
    cF
    @3
    wceq
    cA
    cB
    cF
    ffn
    va
    cA
    cF
    dffn5
    sylib
    ineq1d
    eqtr3d
    @5
    @6
    @7
    @2
    wceq
    #
    wa
    #
    va
    vb
    copab
    #
    @9
    va
    vb
    copab
    #
    cin
    @15
    @9
    wa
    #
    va
    vb
    copab
    @12
    @3
    @16
    @4
    @17
    va
    vb
    cA
    @2
    df-mpt
    va
    vb
    cA
    cB
    df-xp
    ineq12i
    @15
    @9
    va
    vb
    inopab
    @18
    @11
    va
    vb
    @18
    @6
    @14
    @8
    wa
    #
    wa
    #
    @11
    @6
    @14
    @8
    anandi
    @20
    @6
    @8
    @14
    wa
    #
    wa
    @9
    @14
    wa
    @11
    @19
    @21
    @6
    @14
    @8
    ancom
    anbi2i
    @6
    @8
    @14
    anass
    @14
    @10
    @9
    @7
    @2
    eqcom
    anbi2i
    3bitr2i
    bitr3i
    opabbii
    3eqtri
    syl6eq
end

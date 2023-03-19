include "csslt.mm"
include "wbr.mm"
include "cscut.mm"
include "co.mm"
include "cbday.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "wa.mm"
include "csur.mm"
include "crab.mm"
include "cima.mm"
include "cint.mm"
include "wceq.mm"
include "crio.mm"
include "scutval.mm"
include "eqcomd.mm"
include "wcel.mm"
include "wreu.mm"
include "wb.mm"
include "w3a.mm"
include "scutcut.mm"
include "sneq.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "elrab.mm"
include "3anass.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "conway.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "riota2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem scutbday
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A a
  disjoint A b
  disjoint A y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B y
  assert |- ( A <<s B -> ( bday ` ( A |s B ) ) = |^| ( bday " { x e. No | ( A <<s { x } /\ { x } <<s B ) } ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cA
    cB
    cscut
    co
    #
    cbday
    cfv
    #
    cbday
    cA
    vx
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @4
    cB
    csslt
    wbr
    #
    wa
    #
    vx
    csur
    crab
    #
    cima
    cint
    #
    wceq
    #
    vy
    cv
    #
    cbday
    cfv
    #
    @9
    wceq
    #
    vy
    @8
    crio
    #
    @1
    wceq
    #
    @0
    @1
    @14
    vy
    vx
    cA
    cB
    scutval
    eqcomd
    @0
    @1
    @8
    wcel
    #
    @13
    vy
    @8
    wreu
    @10
    @15
    wb
    @0
    @1
    csur
    wcel
    #
    cA
    @1
    csn
    #
    csslt
    wbr
    #
    @18
    cB
    csslt
    wbr
    #
    w3a
    #
    @16
    cA
    cB
    scutcut
    @16
    @17
    @19
    @20
    wa
    #
    wa
    @21
    @7
    @22
    vx
    @1
    csur
    @3
    @1
    wceq
    #
    @5
    @19
    @6
    @20
    @23
    @4
    @18
    cA
    csslt
    @3
    @1
    sneq
    #
    breq2d
    @23
    @4
    @18
    cB
    csslt
    @24
    breq1d
    anbi12d
    elrab
    @17
    @19
    @20
    3anass
    bitr4i
    sylibr
    vy
    vx
    cA
    cB
    conway
    @13
    @10
    vy
    @8
    @1
    @11
    @1
    wceq
    @12
    @2
    @9
    @11
    @1
    cbday
    fveq2
    eqeq1d
    riota2
    syl2anc
    mpbird
end

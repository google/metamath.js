include "wfo.mm"
include "wf.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "crn.mm"
include "wceq.mm"
include "dffo2.mm"
include "simpl.mm"
include "wcel.mm"
include "wex.mm"
include "vex.mm"
include "elrn.mm"
include "eleq2.mm"
include "syl5bbr.mm"
include "biimpar.mm"
include "adantll.mm"
include "wi.mm"
include "wfn.mm"
include "ffn.mm"
include "fnbr.mm"
include "ex.mm"
include "syl.mm"
include "ancrd.mm"
include "eximdv.mm"
include "df-rex.mm"
include "syl6ibr.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "sylbi.mm"
include "cfv.mm"
include "fnbrfvb.mm"
include "biimprd.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "sylan.mm"
include "reximdva.mm"
include "ralimdv.mm"
include "imdistani.mm"
include "dffo3.mm"
include "sylibr.mm"
include "impbii.mm"

theorem dffo4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint F z
  assert |- ( F : A -onto-> B <-> ( F : A --> B /\ A. y e. B E. x e. A x F y ) )

  proof
    cA
    cB
    cF
    wfo
    #
    cA
    cB
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    #
    wa
    #
    @0
    @1
    cF
    crn
    #
    cB
    wceq
    #
    wa
    #
    @7
    cA
    cB
    cF
    dffo2
    @10
    @1
    @6
    @1
    @9
    simpl
    @10
    @5
    vy
    cB
    @10
    @3
    cB
    wcel
    #
    wa
    @4
    vx
    wex
    #
    @5
    @9
    @11
    @12
    @1
    @9
    @12
    @11
    @12
    @3
    @8
    wcel
    @9
    @11
    vx
    @3
    cF
    vy
    vex
    elrn
    @8
    cB
    @3
    eleq2
    syl5bbr
    biimpar
    adantll
    @1
    @12
    @5
    wi
    @9
    @11
    @1
    @12
    @2
    cA
    wcel
    #
    @4
    wa
    #
    vx
    wex
    @5
    @1
    @4
    @14
    vx
    @1
    @4
    @13
    @1
    cF
    cA
    wfn
    #
    @4
    @13
    wi
    cA
    cB
    cF
    ffn
    #
    @15
    @4
    @13
    cA
    @2
    @3
    cF
    fnbr
    ex
    syl
    ancrd
    eximdv
    @4
    vx
    cA
    df-rex
    syl6ibr
    ad2antrr
    mpd
    ralrimiva
    jca
    sylbi
    @7
    @1
    @3
    @2
    cF
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cB
    wral
    #
    wa
    @0
    @1
    @6
    @20
    @1
    @5
    @19
    vy
    cB
    @1
    @4
    @18
    vx
    cA
    @1
    @15
    @13
    @4
    @18
    wi
    @16
    @15
    @13
    wa
    #
    @4
    @17
    @3
    wceq
    #
    @18
    @21
    @22
    @4
    cA
    @2
    @3
    cF
    fnbrfvb
    biimprd
    @17
    @3
    eqcom
    syl6ib
    sylan
    reximdva
    ralimdv
    imdistani
    vx
    vy
    cA
    cB
    cF
    dffo3
    sylibr
    impbii
end

include "wf1.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "fvco3.mm"
include "3ad2antl2.mm"
include "3ad2antl3.mm"
include "eqeq12d.mm"
include "wb.mm"
include "simpl1.mm"
include "ffvelrn.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "wfn.mm"
include "f1f.mm"
include "3ad2ant1.mm"
include "ffn.mm"
include "syl.mm"
include "simp2.mm"
include "fnfco.mm"
include "syl2anc.mm"
include "simp3.mm"
include "eqfnfv.mm"
include "3bitr4d.mm"

theorem cocan1
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let cK: class K
  let vx: setvar x


  assert |- ( ( F : B -1-1-> C /\ H : A --> B /\ K : A --> B ) -> ( ( F o. H ) = ( F o. K ) <-> H = K ) )

  proof
    cB
    cC
    cF
    wf1
    #
    cA
    cB
    cH
    wf
    #
    cA
    cB
    cK
    wf
    #
    w3a
    #
    vx
    cv
    #
    cF
    cH
    ccom
    #
    cfv
    #
    @4
    cF
    cK
    ccom
    #
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @4
    cH
    cfv
    #
    @4
    cK
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @5
    @7
    wceq
    #
    cH
    cK
    wceq
    #
    @3
    @9
    @13
    vx
    cA
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @9
    @11
    cF
    cfv
    #
    @12
    cF
    cfv
    #
    wceq
    #
    @13
    @18
    @6
    @19
    @8
    @20
    @1
    @0
    @17
    @6
    @19
    wceq
    @2
    cA
    cB
    @4
    cF
    cH
    fvco3
    3ad2antl2
    @2
    @0
    @17
    @8
    @20
    wceq
    @1
    cA
    cB
    @4
    cF
    cK
    fvco3
    3ad2antl3
    eqeq12d
    @18
    @0
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @21
    @13
    wb
    @0
    @1
    @2
    @17
    simpl1
    @1
    @0
    @17
    @22
    @2
    cA
    cB
    @4
    cH
    ffvelrn
    3ad2antl2
    @2
    @0
    @17
    @23
    @1
    cA
    cB
    @4
    cK
    ffvelrn
    3ad2antl3
    cB
    cC
    @11
    @12
    cF
    f1fveq
    syl12anc
    bitrd
    ralbidva
    @3
    @5
    cA
    wfn
    #
    @7
    cA
    wfn
    #
    @15
    @10
    wb
    @3
    cF
    cB
    wfn
    #
    @1
    @24
    @3
    cB
    cC
    cF
    wf
    #
    @26
    @0
    @1
    @27
    @2
    cB
    cC
    cF
    f1f
    3ad2ant1
    cB
    cC
    cF
    ffn
    syl
    #
    @0
    @1
    @2
    simp2
    #
    cB
    cA
    cF
    cH
    fnfco
    syl2anc
    @3
    @26
    @2
    @25
    @28
    @0
    @1
    @2
    simp3
    #
    cB
    cA
    cF
    cK
    fnfco
    syl2anc
    vx
    cA
    @5
    @7
    eqfnfv
    syl2anc
    @3
    cH
    cA
    wfn
    #
    cK
    cA
    wfn
    #
    @16
    @14
    wb
    @3
    @1
    @31
    @29
    cA
    cB
    cH
    ffn
    syl
    @3
    @2
    @32
    @30
    cA
    cB
    cK
    ffn
    syl
    vx
    cA
    cH
    cK
    eqfnfv
    syl2anc
    3bitr4d
end

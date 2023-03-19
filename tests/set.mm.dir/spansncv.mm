include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wpss.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "cif.mm"
include "c0v.mm"
include "psseq1.mm"
include "oveq1.mm"
include "sseq2d.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "psseq2.mm"
include "sseq1.mm"
include "eqeq1.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "anbi2d.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "spansncvi.mm"
include "dedth3h.mm"

theorem spansncv
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH /\ C e. ~H ) -> ( ( A C. B /\ B C_ ( A vH ( span ` { C } ) ) ) -> B = ( A vH ( span ` { C } ) ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    chil
    wcel
    #
    cA
    cB
    wpss
    #
    cB
    cA
    cC
    csn
    #
    cspn
    cfv
    #
    chj
    co
    #
    wss
    #
    wa
    #
    cB
    @6
    wceq
    #
    wi
    @0
    cA
    chil
    cif
    #
    cB
    wpss
    #
    cB
    @10
    @5
    chj
    co
    #
    wss
    #
    wa
    #
    cB
    @12
    wceq
    #
    wi
    @10
    @1
    cB
    chil
    cif
    #
    wpss
    #
    @16
    @12
    wss
    #
    wa
    #
    @16
    @12
    wceq
    #
    wi
    @17
    @16
    @10
    @2
    cC
    c0v
    cif
    #
    csn
    #
    cspn
    cfv
    #
    chj
    co
    #
    wss
    #
    wa
    #
    @16
    @24
    wceq
    #
    wi
    cA
    cB
    cC
    chil
    chil
    c0v
    cA
    @10
    wceq
    #
    @8
    @14
    @9
    @15
    @28
    @3
    @11
    @7
    @13
    cA
    @10
    cB
    psseq1
    @28
    @6
    @12
    cB
    cA
    @10
    @5
    chj
    oveq1
    #
    sseq2d
    anbi12d
    @28
    @6
    @12
    cB
    @29
    eqeq2d
    imbi12d
    cB
    @16
    wceq
    #
    @14
    @19
    @15
    @20
    @30
    @11
    @17
    @13
    @18
    cB
    @16
    @10
    psseq2
    cB
    @16
    @12
    sseq1
    anbi12d
    cB
    @16
    @12
    eqeq1
    imbi12d
    cC
    @21
    wceq
    #
    @19
    @26
    @20
    @27
    @31
    @18
    @25
    @17
    @31
    @12
    @24
    @16
    @31
    @5
    @23
    @10
    chj
    @31
    @4
    @22
    cspn
    cC
    @21
    sneq
    fveq2d
    oveq2d
    #
    sseq2d
    anbi2d
    @31
    @12
    @24
    @16
    @32
    eqeq2d
    imbi12d
    @10
    @16
    @21
    cA
    ifchhv
    cB
    ifchhv
    cC
    ifhvhv0
    spansncvi
    dedth3h
end

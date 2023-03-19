include "wfun.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "wral.mm"
include "fdm.mm"
include "cin.mm"
include "dmres.mm"
include "inss2.mm"
include "eqsstri.mm"
include "syl6eqssr.mm"
include "sselda.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "ffvelrn.mm"
include "eqeltrrd.mm"
include "jca.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "simpl.mm"
include "ralimi.mm"
include "dfss3.mm"
include "sylibr.mm"
include "funfn.mm"
include "fnssres.mm"
include "sylanb.mm"
include "sylan2.mm"
include "simpr.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "ralimia.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "ex.mm"
include "impbid2.mm"

theorem ffvresb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( Fun F -> ( ( F |` A ) : A --> B <-> A. x e. A ( x e. dom F /\ ( F ` x ) e. B ) ) )

  proof
    cF
    wfun
    #
    cA
    cB
    cF
    cA
    cres
    #
    wf
    #
    vx
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @3
    cF
    cfv
    #
    cB
    wcel
    #
    wa
    #
    vx
    cA
    wral
    #
    @2
    @8
    vx
    cA
    @2
    @3
    cA
    wcel
    #
    wa
    #
    @5
    @7
    @2
    cA
    @4
    @3
    @2
    cA
    @1
    cdm
    #
    @4
    cA
    cB
    @1
    fdm
    @12
    cA
    @4
    cin
    @4
    cF
    cA
    dmres
    cA
    @4
    inss2
    eqsstri
    syl6eqssr
    sselda
    @11
    @3
    @1
    cfv
    #
    @6
    cB
    @10
    @13
    @6
    wceq
    @2
    @3
    cA
    cF
    fvres
    #
    adantl
    cA
    cB
    @3
    @1
    ffvelrn
    eqeltrrd
    jca
    ralrimiva
    @0
    @9
    @2
    @0
    @9
    wa
    #
    @1
    cA
    wfn
    #
    @1
    crn
    cB
    wss
    #
    @2
    @9
    @0
    cA
    @4
    wss
    #
    @16
    @9
    @5
    vx
    cA
    wral
    @18
    @8
    @5
    vx
    cA
    @5
    @7
    simpl
    ralimi
    vx
    cA
    @4
    dfss3
    sylibr
    @0
    cF
    @4
    wfn
    @18
    @16
    cF
    funfn
    @4
    cA
    cF
    fnssres
    sylanb
    sylan2
    #
    @15
    @16
    @13
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @17
    @19
    @9
    @21
    @0
    @8
    @20
    vx
    cA
    @8
    @20
    @10
    @7
    @5
    @7
    simpr
    @10
    @13
    @6
    cB
    @14
    eleq1d
    syl5ibr
    ralimia
    adantl
    vx
    cA
    cB
    @1
    fnfvrnss
    syl2anc
    cA
    cB
    @1
    df-f
    sylanbrc
    ex
    impbid2
end

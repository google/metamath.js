include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "crest.mm"
include "ccmp.mm"
include "wa.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "oveq2i.mm"
include "simpr.mm"
include "cuni.mm"
include "cin.mm"
include "wss.mm"
include "simpl.mm"
include "inss2.mm"
include "eqid.mm"
include "cnrest.mm"
include "sylancl.mm"
include "cdm.mm"
include "resdmres.mm"
include "dmres.mm"
include "wf.mm"
include "wceq.mm"
include "cnf.mm"
include "fdm.mm"
include "3syl.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "syl5eqr.mm"
include "ctop.mm"
include "cvv.mm"
include "cmptop.mm"
include "adantl.mm"
include "restrcl.mm"
include "restin.mm"
include "oveq1d.mm"
include "3eltr4d.mm"
include "rncmp.mm"
include "syl2anc.mm"
include "syl5eqel.mm"

theorem imacmp
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K


  assert |- ( ( F e. ( J Cn K ) /\ ( J |`t A ) e. Comp ) -> ( K |`t ( F " A ) ) e. Comp )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cJ
    cA
    crest
    co
    #
    ccmp
    wcel
    #
    wa
    #
    cK
    cF
    cA
    cima
    #
    crest
    co
    cK
    cF
    cA
    cres
    #
    crn
    #
    crest
    co
    #
    ccmp
    @4
    @6
    cK
    crest
    cF
    cA
    df-ima
    oveq2i
    @3
    @2
    @5
    @1
    cK
    ccn
    co
    #
    wcel
    @7
    ccmp
    wcel
    @0
    @2
    simpr
    @3
    cF
    cA
    cJ
    cuni
    #
    cin
    #
    cres
    #
    cJ
    @10
    crest
    co
    #
    cK
    ccn
    co
    #
    @5
    @8
    @3
    @0
    @10
    @9
    wss
    @11
    @13
    wcel
    @0
    @2
    simpl
    #
    cA
    @9
    inss2
    @10
    cF
    cJ
    cK
    @9
    @9
    eqid
    #
    cnrest
    sylancl
    @3
    @5
    cF
    @5
    cdm
    #
    cres
    @11
    cF
    cA
    resdmres
    @3
    @16
    @10
    cF
    @3
    @16
    cA
    cF
    cdm
    #
    cin
    @10
    cF
    cA
    dmres
    @3
    @17
    @9
    cA
    @3
    @0
    @9
    cK
    cuni
    #
    cF
    wf
    @17
    @9
    wceq
    @14
    cF
    cJ
    cK
    @9
    @18
    @15
    @18
    eqid
    cnf
    @9
    @18
    cF
    fdm
    3syl
    ineq2d
    syl5eq
    reseq2d
    syl5eqr
    @3
    @1
    @12
    cK
    ccn
    @3
    @1
    ctop
    wcel
    #
    cJ
    cvv
    wcel
    cA
    cvv
    wcel
    wa
    @1
    @12
    wceq
    @2
    @19
    @0
    @1
    cmptop
    adantl
    cA
    cJ
    restrcl
    cA
    cJ
    cvv
    cvv
    @9
    @15
    restin
    3syl
    oveq1d
    3eltr4d
    @5
    @1
    cK
    rncmp
    syl2anc
    syl5eqel
end

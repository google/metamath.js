include "cgru.mm"
include "wcel.mm"
include "wfun.mm"
include "cima.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "crn.mm"
include "wrel.mm"
include "wceq.mm"
include "simpl2.mm"
include "funrel.mm"
include "resres.mm"
include "resdm.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "rneqd.mm"
include "df-ima.mm"
include "syl6reqr.mm"
include "3syl.mm"
include "wf.mm"
include "simpl1.mm"
include "simpr.mm"
include "inss2.mm"
include "a1i.mm"
include "gruss.mm"
include "syl3anc.mm"
include "wfn.mm"
include "wfo.mm"
include "funforn.mm"
include "fof.mm"
include "sylbi.mm"
include "inss1.mm"
include "fssres.mm"
include "sylancl.mm"
include "ffn.mm"
include "simpl3.mm"
include "eqsstr3d.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "grurn.mm"
include "eqeltrd.mm"
include "ex.mm"

theorem gruima
  let cA: class A
  let cU: class U
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( U e. Univ /\ Fun F /\ ( F " A ) C_ U ) -> ( A e. U -> ( F " A ) e. U ) )

  proof
    cU
    cgru
    wcel
    #
    cF
    wfun
    #
    cF
    cA
    cima
    #
    cU
    wss
    #
    w3a
    #
    cA
    cU
    wcel
    #
    @2
    cU
    wcel
    @4
    @5
    wa
    #
    @2
    cF
    cF
    cdm
    #
    cA
    cin
    #
    cres
    #
    crn
    #
    cU
    @6
    @1
    cF
    wrel
    #
    @2
    @10
    wceq
    @0
    @1
    @3
    @5
    simpl2
    #
    cF
    funrel
    @11
    @10
    cF
    cA
    cres
    #
    crn
    @2
    @11
    @9
    @13
    @11
    @9
    cF
    @7
    cres
    #
    cA
    cres
    @13
    cF
    @7
    cA
    resres
    @11
    @14
    cF
    cA
    cF
    resdm
    reseq1d
    syl5eqr
    rneqd
    cF
    cA
    df-ima
    syl6reqr
    3syl
    #
    @6
    @0
    @8
    cU
    wcel
    #
    @8
    cU
    @9
    wf
    #
    @10
    cU
    wcel
    @0
    @1
    @3
    @5
    simpl1
    #
    @6
    @0
    @5
    @8
    cA
    wss
    #
    @16
    @18
    @4
    @5
    simpr
    @19
    @6
    @7
    cA
    inss2
    a1i
    cA
    @8
    cU
    gruss
    syl3anc
    @6
    @9
    @8
    wfn
    #
    @10
    cU
    wss
    @17
    @6
    @1
    @8
    cF
    crn
    #
    @9
    wf
    #
    @20
    @12
    @1
    @7
    @21
    cF
    wf
    #
    @8
    @7
    wss
    @22
    @1
    @7
    @21
    cF
    wfo
    @23
    cF
    funforn
    @7
    @21
    cF
    fof
    sylbi
    @7
    cA
    inss1
    @7
    @21
    @8
    cF
    fssres
    sylancl
    @8
    @21
    @9
    ffn
    3syl
    @6
    @10
    @2
    cU
    @15
    @0
    @1
    @3
    @5
    simpl3
    eqsstr3d
    @8
    cU
    @9
    df-f
    sylanbrc
    @8
    cU
    @9
    grurn
    syl3anc
    eqeltrd
    ex
end

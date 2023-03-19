include "ccnv.mm"
include "wfun.mm"
include "cres.mm"
include "wfo.mm"
include "w3a.mm"
include "cdif.mm"
include "cima.mm"
include "wf1o.mm"
include "cdm.mm"
include "wss.mm"
include "fofun.mm"
include "difss.mm"
include "wf.mm"
include "wceq.mm"
include "fof.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseqr.mm"
include "fores.mm"
include "syl2anc.mm"
include "wb.mm"
include "cin.mm"
include "resres.mm"
include "indif.mm"
include "reseq2i.mm"
include "eqtri.mm"
include "foeq1.mm"
include "ax-mp.mm"
include "crn.mm"
include "rneqi.mm"
include "df-ima.mm"
include "3eqtr4i.mm"
include "foeq3.mm"
include "bitri.mm"
include "sylib.mm"
include "funres11.mm"
include "wa.mm"
include "dff1o3.mm"
include "biimpri.mm"
include "syl2anr.mm"
include "3adant3.mm"
include "forn.mm"
include "syl5eq.mm"
include "anim12i.mm"
include "imadif.mm"
include "difeq12.mm"
include "sylan9eq.mm"
include "sylan2.mm"
include "3impb.mm"
include "f1oeq3d.mm"
include "mpbid.mm"

theorem resdif
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( Fun `' F /\ ( F |` A ) : A -onto-> C /\ ( F |` B ) : B -onto-> D ) -> ( F |` ( A \ B ) ) : ( A \ B ) -1-1-onto-> ( C \ D ) )

  proof
    cF
    ccnv
    wfun
    #
    cA
    cC
    cF
    cA
    cres
    #
    wfo
    #
    cB
    cD
    cF
    cB
    cres
    #
    wfo
    #
    w3a
    #
    cA
    cB
    cdif
    #
    cF
    @6
    cima
    #
    cF
    @6
    cres
    #
    wf1o
    #
    @6
    cC
    cD
    cdif
    #
    @8
    wf1o
    @0
    @2
    @9
    @4
    @2
    @6
    @7
    @8
    wfo
    #
    @8
    ccnv
    wfun
    #
    @9
    @0
    @2
    @6
    @1
    @6
    cima
    #
    @1
    @6
    cres
    #
    wfo
    #
    @11
    @2
    @1
    wfun
    @6
    @1
    cdm
    #
    wss
    @15
    cA
    cC
    @1
    fofun
    @2
    cA
    @6
    @16
    cA
    cB
    difss
    @2
    cA
    cC
    @1
    wf
    @16
    cA
    wceq
    cA
    cC
    @1
    fof
    cA
    cC
    @1
    fdm
    syl
    syl5sseqr
    @6
    @1
    fores
    syl2anc
    @15
    @6
    @13
    @8
    wfo
    #
    @11
    @14
    @8
    wceq
    @15
    @17
    wb
    @14
    cF
    cA
    @6
    cin
    #
    cres
    @8
    cF
    cA
    @6
    resres
    @18
    @6
    cF
    cA
    cB
    indif
    reseq2i
    eqtri
    #
    @6
    @13
    @14
    @8
    foeq1
    ax-mp
    @13
    @7
    wceq
    @17
    @11
    wb
    @14
    crn
    @8
    crn
    @13
    @7
    @14
    @8
    @19
    rneqi
    @1
    @6
    df-ima
    cF
    @6
    df-ima
    3eqtr4i
    @13
    @7
    @6
    @8
    foeq3
    ax-mp
    bitri
    sylib
    @6
    cF
    funres11
    @9
    @11
    @12
    wa
    @6
    @7
    @8
    dff1o3
    biimpri
    syl2anr
    3adant3
    @5
    @7
    @10
    @6
    @8
    @0
    @2
    @4
    @7
    @10
    wceq
    #
    @2
    @4
    wa
    @0
    cF
    cA
    cima
    #
    cC
    wceq
    #
    cF
    cB
    cima
    #
    cD
    wceq
    #
    wa
    #
    @20
    @2
    @22
    @4
    @24
    @2
    @21
    @1
    crn
    cC
    cF
    cA
    df-ima
    cA
    cC
    @1
    forn
    syl5eq
    @4
    @23
    @3
    crn
    cD
    cF
    cB
    df-ima
    cB
    cD
    @3
    forn
    syl5eq
    anim12i
    @0
    @25
    @7
    @21
    @23
    cdif
    @10
    cA
    cB
    cF
    imadif
    @21
    cC
    @23
    cD
    difeq12
    sylan9eq
    sylan2
    3impb
    f1oeq3d
    mpbid
end

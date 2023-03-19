include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "c2nd.mm"
include "cres.mm"
include "wfo.mm"
include "ccnv.mm"
include "wfun.mm"
include "wf1o.mm"
include "c0.mm"
include "wne.mm"
include "snnzg.mm"
include "fo2ndres.mm"
include "syl.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "moeq.mm"
include "moani.mm"
include "vex.mm"
include "brres.mm"
include "cfv.mm"
include "cvv.mm"
include "wfn.mm"
include "wb.mm"
include "fo2nd.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "anbi1i.mm"
include "c1st.mm"
include "elxp7.mm"
include "eleq1.mm"
include "biimpa.mm"
include "adantrl.mm"
include "elsni.mm"
include "eqopi.mm"
include "ancom2s.mm"
include "an12s.mm"
include "sylanr2.mm"
include "adantrrr.mm"
include "jca.mm"
include "sylan2b.mm"
include "adantl.mm"
include "fveq2.mm"
include "op2ndg.mm"
include "mpan2.mm"
include "sylan9eqr.mm"
include "simprr.mm"
include "snidg.mm"
include "adantr.mm"
include "simprl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "impbida.mm"
include "syl5bbr.mm"
include "syl5bb.mm"
include "mobidv.mm"
include "mpbiri.mm"
include "alrimiv.mm"
include "funcnv2.mm"
include "sylibr.mm"
include "dff1o3.mm"
include "sylanbrc.mm"

theorem 2ndconst
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( 2nd |` ( { A } X. B ) ) : ( { A } X. B ) -1-1-onto-> B )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
    cB
    cxp
    #
    cB
    c2nd
    @2
    cres
    #
    wfo
    #
    @3
    ccnv
    wfun
    #
    @2
    cB
    @3
    wf1o
    @0
    @1
    c0
    wne
    @4
    cA
    cV
    snnzg
    @1
    cB
    fo2ndres
    syl
    @0
    vx
    cv
    #
    vy
    cv
    #
    @3
    wbr
    #
    vx
    wmo
    #
    vy
    wal
    @5
    @0
    @9
    vy
    @0
    @9
    @7
    cB
    wcel
    #
    @6
    cA
    @7
    cop
    #
    wceq
    #
    wa
    #
    vx
    wmo
    @12
    @10
    vx
    vx
    @11
    moeq
    moani
    @0
    @8
    @13
    vx
    @8
    @6
    @7
    c2nd
    wbr
    #
    @6
    @2
    wcel
    #
    wa
    #
    @0
    @13
    @6
    @7
    c2nd
    @2
    vy
    vex
    #
    brres
    @16
    @6
    c2nd
    cfv
    #
    @7
    wceq
    #
    @15
    wa
    #
    @0
    @13
    @19
    @14
    @15
    c2nd
    cvv
    wfn
    #
    @6
    cvv
    wcel
    @19
    @14
    wb
    cvv
    cvv
    c2nd
    wfo
    @21
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    ax-mp
    vx
    vex
    cvv
    @6
    @7
    c2nd
    fnbrfvb
    mp2an
    anbi1i
    @0
    @20
    @13
    @20
    @13
    @0
    @15
    @19
    @6
    cvv
    cvv
    cxp
    wcel
    #
    @6
    c1st
    cfv
    #
    @1
    wcel
    #
    @18
    cB
    wcel
    #
    wa
    #
    wa
    #
    @13
    @6
    @1
    cB
    elxp7
    @19
    @27
    wa
    @10
    @12
    @19
    @26
    @10
    @22
    @19
    @25
    @10
    @24
    @19
    @25
    @10
    @18
    @7
    cB
    eleq1
    biimpa
    adantrl
    adantrl
    @19
    @22
    @24
    @12
    @25
    @24
    @19
    @22
    @23
    cA
    wceq
    #
    @12
    @23
    cA
    elsni
    @22
    @19
    @28
    @12
    @22
    @28
    @19
    @12
    @6
    cA
    @7
    cvv
    cvv
    eqopi
    ancom2s
    an12s
    sylanr2
    adantrrr
    jca
    sylan2b
    adantl
    @0
    @13
    wa
    #
    @19
    @15
    @0
    @12
    @19
    @10
    @12
    @0
    @18
    @11
    c2nd
    cfv
    #
    @7
    @6
    @11
    c2nd
    fveq2
    @0
    @7
    cvv
    wcel
    @30
    @7
    wceq
    @17
    cA
    @7
    cV
    cvv
    op2ndg
    mpan2
    sylan9eqr
    adantrl
    @29
    @6
    @11
    @2
    @0
    @10
    @12
    simprr
    @29
    cA
    @1
    wcel
    #
    @10
    @11
    @2
    wcel
    @0
    @31
    @13
    cA
    cV
    snidg
    adantr
    @0
    @10
    @12
    simprl
    cA
    @7
    @1
    cB
    opelxpi
    syl2anc
    eqeltrd
    jca
    impbida
    syl5bbr
    syl5bb
    mobidv
    mpbiri
    alrimiv
    vx
    vy
    @3
    funcnv2
    sylibr
    @2
    cB
    @3
    dff1o3
    sylanbrc
end

include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "c1st.mm"
include "cres.mm"
include "wfo.mm"
include "ccnv.mm"
include "wfun.mm"
include "wf1o.mm"
include "c0.mm"
include "wne.mm"
include "snnzg.mm"
include "fo1stres.mm"
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
include "fo1st.mm"
include "fofn.mm"
include "ax-mp.mm"
include "fnbrfvb.mm"
include "mp2an.mm"
include "anbi1i.mm"
include "c2nd.mm"
include "elxp7.mm"
include "eleq1.mm"
include "biimpa.mm"
include "adantrr.mm"
include "adantrl.mm"
include "elsni.mm"
include "eqopi.mm"
include "an12s.mm"
include "sylanr2.mm"
include "adantrrl.mm"
include "jca.mm"
include "sylan2b.mm"
include "adantl.mm"
include "simprr.mm"
include "fveq2d.mm"
include "simprl.mm"
include "simpl.mm"
include "op1stg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "snidg.mm"
include "adantr.mm"
include "opelxpi.mm"
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

theorem 1stconst
  let cA: class A
  let cB: class B
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( B e. V -> ( 1st |` ( A X. { B } ) ) : ( A X. { B } ) -1-1-onto-> A )

  proof
    cB
    cV
    wcel
    #
    cA
    cB
    csn
    #
    cxp
    #
    cA
    c1st
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
    cA
    @3
    wf1o
    @0
    @1
    c0
    wne
    @4
    cB
    cV
    snnzg
    cA
    @1
    fo1stres
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
    cA
    wcel
    #
    @6
    @7
    cB
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
    c1st
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
    c1st
    @2
    vy
    vex
    brres
    @16
    @6
    c1st
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
    @18
    @14
    @15
    c1st
    cvv
    wfn
    #
    @6
    cvv
    wcel
    @18
    @14
    wb
    cvv
    cvv
    c1st
    wfo
    @20
    fo1st
    cvv
    cvv
    c1st
    fofn
    ax-mp
    vx
    vex
    cvv
    @6
    @7
    c1st
    fnbrfvb
    mp2an
    anbi1i
    @0
    @19
    @13
    @19
    @13
    @0
    @15
    @18
    @6
    cvv
    cvv
    cxp
    wcel
    #
    @17
    cA
    wcel
    #
    @6
    c2nd
    cfv
    #
    @1
    wcel
    #
    wa
    #
    wa
    #
    @13
    @6
    cA
    @1
    elxp7
    @18
    @26
    wa
    @10
    @12
    @18
    @25
    @10
    @21
    @18
    @22
    @10
    @24
    @18
    @22
    @10
    @17
    @7
    cA
    eleq1
    biimpa
    adantrr
    adantrl
    @18
    @21
    @24
    @12
    @22
    @24
    @18
    @21
    @23
    cB
    wceq
    #
    @12
    @23
    cB
    elsni
    @21
    @18
    @27
    @12
    @6
    @7
    cB
    cvv
    cvv
    eqopi
    an12s
    sylanr2
    adantrrl
    jca
    sylan2b
    adantl
    @0
    @13
    wa
    #
    @18
    @15
    @28
    @17
    @11
    c1st
    cfv
    #
    @7
    @28
    @6
    @11
    c1st
    @0
    @10
    @12
    simprr
    #
    fveq2d
    @28
    @10
    @0
    @29
    @7
    wceq
    @0
    @10
    @12
    simprl
    #
    @0
    @13
    simpl
    @7
    cB
    cA
    cV
    op1stg
    syl2anc
    eqtrd
    @28
    @6
    @11
    @2
    @30
    @28
    @10
    cB
    @1
    wcel
    #
    @11
    @2
    wcel
    @31
    @0
    @32
    @13
    cB
    cV
    snidg
    adantr
    @7
    cB
    cA
    @1
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
    cA
    @3
    dff1o3
    sylanbrc
end

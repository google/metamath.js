include "cnq.mm"
include "wcel.mm"
include "cvv.mm"
include "crq.mm"
include "cfv.mm"
include "wceq.mm"
include "cmq.mm"
include "co.mm"
include "c1q.mm"
include "fvex.mm"
include "a1i.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "wi.mm"
include "wa.mm"
include "id.mm"
include "1nq.mm"
include "syl6eqel.mm"
include "cxp.mm"
include "mulnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "simprd.mm"
include "elex.mm"
include "wb.mm"
include "cv.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "wex.mm"
include "weu.mm"
include "c2nd.mm"
include "c1st.mm"
include "cop.mm"
include "cerq.mm"
include "cmpq.mm"
include "cmi.mm"
include "nqerid.mm"
include "cnpi.mm"
include "wrel.mm"
include "relxp.mm"
include "elpqn.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "mulerpq.mm"
include "syl6eq.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "mulpipq.mm"
include "syl22anc.mm"
include "mulcompi.mm"
include "opeq2i.mm"
include "ax-mp.mm"
include "ceq.mm"
include "wbr.mm"
include "mulclpi.mm"
include "syl2anc.mm"
include "1nqenq.mm"
include "opelxpi.mm"
include "nqereq.mm"
include "mpbid.mm"
include "syl5reqr.mm"
include "3eqtrd.mm"
include "spcev.mm"
include "wmo.mm"
include "mulcomnq.mm"
include "mulassnq.mm"
include "mulidnq.mm"
include "caovmo.mm"
include "eu5.mm"
include "mpbiran2.mm"
include "sylibr.mm"
include "copab.mm"
include "wtru.mm"
include "wss.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "df-rq.mm"
include "eqcomi.mm"
include "3sstr4i.mm"
include "relss.mm"
include "mp2.mm"
include "eleq2i.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "ancom.mm"
include "mpbiri.mm"
include "simpld.mm"
include "2thd.mm"
include "pm5.32i.mm"
include "df-ov.mm"
include "eqeq1i.mm"
include "anbi1i.mm"
include "3bitr2ri.mm"
include "bitri.mm"
include "3bitri.mm"
include "opabbi2dv.mm"
include "trud.mm"
include "fvopab3g.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem recmulnq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t


  assert |- ( A e. Q. -> ( ( *Q ` A ) = B <-> ( A .Q B ) = 1Q ) )

  proof
    cA
    cnq
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    crq
    cfv
    #
    cB
    wceq
    #
    cA
    cB
    cmq
    co
    #
    c1q
    wceq
    #
    @0
    @2
    cvv
    wcel
    #
    @3
    @1
    @6
    @0
    cA
    crq
    fvex
    a1i
    @2
    cB
    cvv
    eleq1
    syl5ibcom
    @5
    @1
    wi
    @0
    @5
    cB
    cnq
    wcel
    #
    @1
    @5
    @0
    @7
    @5
    @4
    cnq
    wcel
    @0
    @7
    wa
    @5
    @4
    c1q
    cnq
    @5
    id
    1nq
    syl6eqel
    cA
    cB
    cnq
    cmq
    cnq
    cnq
    cxp
    #
    cnq
    cmq
    mulnqf
    fdmi
    #
    0nnq
    ndmovrcl
    syl
    simprd
    cB
    cnq
    elex
    syl
    a1i
    @0
    @1
    @3
    @5
    wb
    vx
    cv
    #
    vy
    cv
    #
    cmq
    co
    #
    c1q
    wceq
    #
    cA
    @11
    cmq
    co
    #
    c1q
    wceq
    @5
    vx
    vy
    cA
    cB
    cnq
    cvv
    crq
    @10
    cA
    wceq
    @12
    @14
    c1q
    @10
    cA
    @11
    cmq
    oveq1
    eqeq1d
    @11
    cB
    wceq
    @14
    @4
    c1q
    @11
    cB
    cA
    cmq
    oveq2
    eqeq1d
    @10
    cnq
    wcel
    #
    @13
    vy
    wex
    #
    @13
    vy
    weu
    #
    @15
    @10
    @10
    c2nd
    cfv
    #
    @10
    c1st
    cfv
    #
    cop
    #
    cerq
    cfv
    #
    cmq
    co
    #
    c1q
    wceq
    #
    @16
    @15
    @22
    @19
    @18
    cop
    #
    @20
    cmpq
    co
    #
    cerq
    cfv
    #
    @19
    @18
    cmi
    co
    #
    @27
    cop
    #
    cerq
    cfv
    #
    c1q
    @15
    @22
    @24
    cerq
    cfv
    #
    @21
    cmq
    co
    @26
    @15
    @10
    @30
    @21
    cmq
    @15
    @10
    cerq
    cfv
    @10
    @30
    @10
    nqerid
    @15
    @10
    @24
    cerq
    @15
    cnpi
    cnpi
    cxp
    #
    wrel
    @10
    @31
    wcel
    #
    @10
    @24
    wceq
    cnpi
    cnpi
    relxp
    @10
    elpqn
    #
    @10
    @31
    1st2nd
    sylancr
    fveq2d
    eqtr3d
    oveq1d
    @24
    @20
    mulerpq
    syl6eq
    @15
    @25
    @28
    cerq
    @15
    @25
    @27
    @18
    @19
    cmi
    co
    #
    cop
    #
    @28
    @15
    @19
    cnpi
    wcel
    #
    @18
    cnpi
    wcel
    #
    @37
    @36
    @25
    @35
    wceq
    @15
    @32
    @36
    @33
    @10
    cnpi
    cnpi
    xp1st
    syl
    #
    @15
    @32
    @37
    @33
    @10
    cnpi
    cnpi
    xp2nd
    syl
    #
    @39
    @38
    @19
    @18
    @18
    @19
    mulpipq
    syl22anc
    @34
    @27
    @27
    @18
    @19
    mulcompi
    opeq2i
    syl6eq
    fveq2d
    @15
    c1q
    c1q
    cerq
    cfv
    #
    @29
    c1q
    cnq
    wcel
    #
    @40
    c1q
    wceq
    1nq
    c1q
    nqerid
    ax-mp
    @15
    c1q
    @28
    ceq
    wbr
    #
    @40
    @29
    wceq
    #
    @15
    @27
    cnpi
    wcel
    #
    @42
    @15
    @36
    @37
    @44
    @38
    @39
    @19
    @18
    mulclpi
    syl2anc
    #
    @27
    1nqenq
    syl
    @15
    c1q
    @31
    wcel
    #
    @28
    @31
    wcel
    #
    @42
    @43
    wb
    @41
    @46
    1nq
    c1q
    elpqn
    ax-mp
    @15
    @44
    @44
    @47
    @45
    @45
    @27
    @27
    cnpi
    cnpi
    opelxpi
    syl2anc
    c1q
    @28
    nqereq
    sylancr
    mpbid
    syl5reqr
    3eqtrd
    @13
    @23
    vy
    @21
    @20
    cerq
    fvex
    @11
    @21
    wceq
    @12
    @22
    c1q
    @11
    @21
    @10
    cmq
    oveq2
    eqeq1d
    spcev
    syl
    @17
    @16
    @13
    vy
    wmo
    vr
    vs
    vt
    vy
    @10
    c1q
    cnq
    cmq
    1nq
    @9
    0nnq
    vr
    cv
    #
    vs
    cv
    #
    mulcomnq
    @48
    @49
    vt
    cv
    mulassnq
    @48
    mulidnq
    caovmo
    @13
    vy
    eu5
    mpbiran2
    sylibr
    crq
    @15
    @13
    wa
    #
    vx
    vy
    copab
    wceq
    wtru
    @50
    vx
    vy
    crq
    crq
    @8
    wss
    @8
    wrel
    crq
    wrel
    cmq
    ccnv
    c1q
    csn
    #
    cima
    #
    cmq
    cdm
    #
    crq
    @8
    cmq
    @51
    cnvimass
    df-rq
    @53
    @8
    @9
    eqcomi
    3sstr4i
    cnq
    cnq
    relxp
    crq
    @8
    relss
    mp2
    @10
    @11
    cop
    #
    crq
    wcel
    #
    @50
    wb
    wtru
    @55
    @54
    @52
    wcel
    #
    @54
    @8
    wcel
    #
    @54
    cmq
    cfv
    #
    c1q
    wceq
    #
    wa
    #
    @50
    crq
    @52
    @54
    df-rq
    eleq2i
    @8
    cnq
    cmq
    wf
    cmq
    @8
    wfn
    @56
    @60
    wb
    mulnqf
    @8
    cnq
    cmq
    ffn
    @8
    c1q
    @54
    cmq
    fniniseg
    mp2b
    @60
    @59
    @57
    wa
    #
    @50
    @57
    @59
    ancom
    @50
    @13
    @15
    wa
    @13
    @57
    wa
    @61
    @15
    @13
    ancom
    @13
    @57
    @15
    @13
    @57
    @15
    @13
    @15
    @11
    cnq
    wcel
    #
    wa
    #
    @57
    @13
    @12
    cnq
    wcel
    #
    @63
    @13
    @64
    @41
    1nq
    @12
    c1q
    cnq
    eleq1
    mpbiri
    @10
    @11
    cnq
    cmq
    @9
    0nnq
    ndmovrcl
    syl
    #
    @10
    @11
    cnq
    cnq
    opelxpi
    syl
    @13
    @15
    @62
    @65
    simpld
    2thd
    pm5.32i
    @13
    @59
    @57
    @12
    @58
    c1q
    @10
    @11
    cmq
    df-ov
    eqeq1i
    anbi1i
    3bitr2ri
    bitri
    3bitri
    a1i
    opabbi2dv
    trud
    fvopab3g
    ex
    pm5.21ndd
end

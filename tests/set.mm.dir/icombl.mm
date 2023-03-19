include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cdm.mm"
include "cpnf.mm"
include "cdif.mm"
include "cun.mm"
include "wceq.mm"
include "uncom.mm"
include "cle.mm"
include "rexr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "wi.mm"
include "xrltle.mm"
include "sylan.mm"
include "imp.mm"
include "pnfge.mm"
include "syl.mm"
include "icoun.mm"
include "syl32anc.mm"
include "syl5eq.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wb.mm"
include "ssun1.mm"
include "syl5sseq.mm"
include "incom.mm"
include "icodisj.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "uneqdifeq.mm"
include "mpbid.mm"
include "icombl1.mm"
include "wo.mm"
include "xrleloe.mm"
include "simpr.mm"
include "w3a.mm"
include "xrre2.mm"
include "expr.mm"
include "syl31anc.mm"
include "orim1d.mm"
include "mpd.mm"
include "oveq1.mm"
include "ax-mp.mm"
include "ico0.mm"
include "mp2an.mm"
include "mpbir.mm"
include "syl6eq.mm"
include "0mbl.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "difmbl.mm"
include "eqeltrrd.mm"
include "wn.mm"
include "adantr.mm"
include "xrlenlt.mm"
include "bitrd.mm"
include "biimpar.mm"
include "pm2.61dan.mm"

theorem icombl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR* ) -> ( A [,) B ) e. dom vol )

  proof
    cA
    cr
    wcel
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cico
    co
    #
    cvol
    cdm
    #
    wcel
    @2
    @3
    wa
    #
    cA
    cpnf
    cico
    co
    #
    cB
    cpnf
    cico
    co
    #
    cdif
    #
    @4
    @5
    @6
    @8
    @4
    cun
    #
    @7
    wceq
    #
    @9
    @4
    wceq
    #
    @6
    @10
    @4
    @8
    cun
    #
    @7
    @8
    @4
    uncom
    @6
    cA
    cxr
    wcel
    #
    @1
    cpnf
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cpnf
    cle
    wbr
    #
    @13
    @7
    wceq
    @0
    @14
    @1
    @3
    cA
    rexr
    #
    ad2antrr
    #
    @0
    @1
    @3
    simplr
    #
    @15
    @6
    pnfxr
    a1i
    #
    @2
    @3
    @16
    @0
    @14
    @1
    @3
    @16
    wi
    @18
    cA
    cB
    xrltle
    sylan
    imp
    @6
    @1
    @17
    @20
    cB
    pnfge
    syl
    #
    cA
    cB
    cpnf
    icoun
    syl32anc
    syl5eq
    #
    @6
    @8
    @7
    wss
    @8
    @4
    cin
    #
    c0
    wceq
    @11
    @12
    wb
    @6
    @10
    @8
    @7
    @8
    @4
    ssun1
    @23
    syl5sseq
    @6
    @24
    @4
    @8
    cin
    #
    c0
    @8
    @4
    incom
    @6
    @14
    @1
    @25
    c0
    wceq
    #
    @19
    @20
    @14
    @1
    @15
    @26
    pnfxr
    cA
    cB
    cpnf
    icodisj
    mp3an3
    syl2anc
    syl5eq
    @8
    @4
    @7
    uneqdifeq
    syl2anc
    mpbid
    @6
    @7
    @5
    wcel
    #
    @8
    @5
    wcel
    #
    @9
    @5
    wcel
    @0
    @27
    @1
    @3
    cA
    icombl1
    ad2antrr
    @6
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    wo
    #
    @28
    @6
    cB
    cpnf
    clt
    wbr
    #
    @30
    wo
    #
    @31
    @6
    @17
    @33
    @22
    @6
    @1
    @15
    @17
    @33
    wb
    @20
    @21
    cB
    cpnf
    xrleloe
    syl2anc
    mpbid
    @6
    @32
    @29
    @30
    @6
    @14
    @1
    @15
    @3
    @32
    @29
    wi
    @19
    @20
    @21
    @2
    @3
    simpr
    @14
    @1
    @15
    w3a
    @3
    @32
    @29
    cA
    cB
    cpnf
    xrre2
    expr
    syl31anc
    orim1d
    mpd
    @29
    @28
    @30
    cB
    icombl1
    @30
    @8
    c0
    @5
    @30
    @8
    cpnf
    cpnf
    cico
    co
    #
    c0
    cB
    cpnf
    cpnf
    cico
    oveq1
    @34
    c0
    wceq
    #
    cpnf
    cpnf
    cle
    wbr
    #
    @15
    @36
    pnfxr
    cpnf
    pnfge
    ax-mp
    @15
    @15
    @35
    @36
    wb
    pnfxr
    pnfxr
    cpnf
    cpnf
    ico0
    mp2an
    mpbir
    syl6eq
    0mbl
    syl6eqel
    jaoi
    syl
    @7
    @8
    difmbl
    syl2anc
    eqeltrrd
    @2
    @3
    wn
    #
    wa
    @4
    c0
    @5
    @2
    @4
    c0
    wceq
    #
    @37
    @2
    @38
    cB
    cA
    cle
    wbr
    #
    @37
    @0
    @14
    @1
    @38
    @39
    wb
    @18
    cA
    cB
    ico0
    sylan
    @2
    @1
    @14
    @39
    @37
    wb
    @0
    @1
    simpr
    @0
    @14
    @1
    @18
    adantr
    cB
    cA
    xrlenlt
    syl2anc
    bitrd
    biimpar
    0mbl
    syl6eqel
    pm2.61dan
end

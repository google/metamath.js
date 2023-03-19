include "con0.mm"
include "ct1.mm"
include "cin.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "csuc.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "wn.mm"
include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "wral.mm"
include "ctop.mm"
include "eqid.mm"
include "ist1.mm"
include "simprbi.mm"
include "onelon.mm"
include "ex.mm"
include "wne.mm"
include "wb.mm"
include "neldifsnd.mm"
include "p0ex.mm"
include "prid2.mm"
include "df2o2.mm"
include "eleqtrri.mm"
include "elunii.mm"
include "mpan.mm"
include "df1o2.mm"
include "1on.mm"
include "eqeltrri.mm"
include "onirri.mm"
include "a1i.mm"
include "eldifd.mm"
include "ne0i.mm"
include "syl.mm"
include "2thd.mm"
include "nbbn.mm"
include "sylib.mm"
include "on0eln0.mm"
include "nsyl.mm"
include "nsyli.mm"
include "imp.mm"
include "0ex.mm"
include "prid1.mm"
include "adantl.mm"
include "wceq.mm"
include "simpr.mm"
include "sneqd.mm"
include "eleq1d.mm"
include "rspcdv.mm"
include "cldopn.mm"
include "syl6.mm"
include "mtod.mm"
include "con2d.mm"
include "syl5.mm"
include "2on.mm"
include "wss.mm"
include "ontri1.mm"
include "onsssuc.mm"
include "bitr3d.mm"
include "mpan2.mm"
include "sylibd.mm"
include "0ntop.mm"
include "t1top.mm"
include "mto.mm"
include "nelneq.mm"
include "elsni.mm"
include "sylbi.mm"
include "ssriv.mm"
include "cun.mm"
include "df-suc.mm"
include "difeq1i.mm"
include "difundir.mm"
include "eqtri.mm"
include "df-pr.mm"
include "df2o3.mm"
include "difid.mm"
include "1n0.mm"
include "disjsn2.mm"
include "ax-mp.mm"
include "difeq2i.mm"
include "difin.mm"
include "dif0.mm"
include "3eqtr3i.mm"
include "uneq12i.mm"
include "uncom.mm"
include "un0.mm"
include "3eqtri.mm"
include "2on0.mm"
include "eqtr4i.mm"
include "sseqtri.mm"
include "cha.mm"
include "ssoninhaus.mm"
include "haust1.mm"
include "sslin.mm"
include "sstri.mm"
include "eqssi.mm"

theorem onint1
  let va: setvar a
  let vj: setvar j


  assert |- ( On i^i Fre ) = { 1o , 2o }

  proof
    con0
    ct1
    cin
    #
    c1o
    c2o
    cpr
    #
    @0
    c2o
    csuc
    #
    c0
    csn
    #
    cdif
    #
    @1
    vj
    @0
    @4
    vj
    cv
    #
    @0
    wcel
    @5
    con0
    wcel
    #
    @5
    ct1
    wcel
    #
    wa
    #
    @5
    @4
    wcel
    @5
    con0
    ct1
    elin
    @8
    @5
    @2
    @3
    @6
    @7
    @5
    @2
    wcel
    #
    @6
    @7
    c2o
    @5
    wcel
    #
    wn
    #
    @9
    @7
    va
    cv
    #
    csn
    #
    @5
    ccld
    cfv
    #
    wcel
    #
    va
    @5
    cuni
    #
    wral
    #
    @6
    @11
    @7
    @5
    ctop
    wcel
    @17
    @5
    @16
    va
    @16
    eqid
    #
    ist1
    simprbi
    @6
    @10
    @17
    @6
    @10
    @17
    wn
    @6
    @10
    wa
    #
    @17
    @16
    @3
    cdif
    #
    @5
    wcel
    #
    @6
    @10
    @21
    wn
    @6
    @21
    @20
    con0
    wcel
    #
    @10
    @6
    @21
    @22
    @5
    @20
    onelon
    ex
    @10
    c0
    @20
    wcel
    #
    @20
    c0
    wne
    #
    wb
    #
    @22
    @10
    @23
    wn
    #
    @24
    wb
    @25
    wn
    @10
    @26
    @24
    @10
    c0
    @16
    neldifsnd
    @10
    @3
    @20
    wcel
    @24
    @10
    @3
    @16
    @3
    @3
    c2o
    wcel
    @10
    @3
    @16
    wcel
    @3
    c0
    @3
    cpr
    #
    c2o
    c0
    @3
    p0ex
    prid2
    df2o2
    eleqtrri
    @3
    c2o
    @5
    elunii
    mpan
    @3
    @3
    wcel
    wn
    @10
    @3
    c1o
    @3
    con0
    df1o2
    1on
    eqeltrri
    onirri
    a1i
    eldifd
    @20
    @3
    ne0i
    syl
    2thd
    @23
    @24
    nbbn
    sylib
    @20
    on0eln0
    nsyl
    nsyli
    imp
    @19
    @17
    @3
    @14
    wcel
    #
    @21
    @19
    @15
    @28
    va
    c0
    @16
    @10
    c0
    @16
    wcel
    #
    @6
    c0
    c2o
    wcel
    @10
    @29
    c0
    @27
    c2o
    c0
    @3
    0ex
    prid1
    df2o2
    eleqtrri
    c0
    c2o
    @5
    elunii
    mpan
    adantl
    @19
    @12
    c0
    wceq
    #
    wa
    #
    @13
    @3
    @14
    @31
    @12
    c0
    @19
    @30
    simpr
    sneqd
    eleq1d
    rspcdv
    @3
    @5
    @16
    @18
    cldopn
    syl6
    mtod
    ex
    con2d
    syl5
    @6
    c2o
    con0
    wcel
    #
    @11
    @9
    wb
    2on
    @6
    @32
    wa
    @5
    c2o
    wss
    @11
    @9
    @5
    c2o
    ontri1
    @5
    c2o
    onsssuc
    bitr3d
    mpan2
    sylibd
    imp
    @7
    @5
    @3
    wcel
    #
    wn
    @6
    @7
    @5
    c0
    wceq
    #
    @33
    @7
    c0
    ct1
    wcel
    #
    wn
    @34
    wn
    @35
    c0
    ctop
    wcel
    0ntop
    c0
    t1top
    mto
    @5
    c0
    ct1
    nelneq
    mpan2
    @5
    c0
    elsni
    nsyl
    adantl
    eldifd
    sylbi
    ssriv
    @4
    c2o
    @3
    cdif
    #
    c2o
    csn
    #
    @3
    cdif
    #
    cun
    #
    @1
    @4
    c2o
    @37
    cun
    #
    @3
    cdif
    @39
    @2
    @40
    @3
    c2o
    df-suc
    difeq1i
    c2o
    @37
    @3
    difundir
    eqtri
    @1
    c1o
    csn
    #
    @37
    cun
    @39
    c1o
    c2o
    df-pr
    @36
    @41
    @38
    @37
    @36
    @3
    @41
    cun
    #
    @3
    cdif
    @3
    @3
    cdif
    #
    @41
    @3
    cdif
    #
    cun
    #
    @41
    c2o
    @42
    @3
    c2o
    c0
    c1o
    cpr
    @42
    df2o3
    c0
    c1o
    df-pr
    eqtri
    difeq1i
    @3
    @41
    @3
    difundir
    @45
    c0
    @41
    cun
    @41
    c0
    cun
    @41
    @43
    c0
    @44
    @41
    @3
    difid
    @41
    @41
    @3
    cin
    #
    cdif
    @41
    c0
    cdif
    @44
    @41
    @46
    c0
    @41
    c1o
    c0
    wne
    @46
    c0
    wceq
    1n0
    c1o
    c0
    disjsn2
    ax-mp
    difeq2i
    @41
    @3
    difin
    @41
    dif0
    3eqtr3i
    uneq12i
    c0
    @41
    uncom
    @41
    un0
    3eqtri
    3eqtri
    @37
    @37
    @3
    cin
    #
    cdif
    @37
    c0
    cdif
    @38
    @37
    @47
    c0
    @37
    c2o
    c0
    wne
    @47
    c0
    wceq
    2on0
    c2o
    c0
    disjsn2
    ax-mp
    difeq2i
    @37
    @3
    difin
    @37
    dif0
    3eqtr3i
    uneq12i
    eqtr4i
    eqtr4i
    sseqtri
    @1
    con0
    cha
    cin
    #
    @0
    ssoninhaus
    cha
    ct1
    wss
    @48
    @0
    wss
    vj
    cha
    ct1
    @5
    haust1
    ssriv
    cha
    ct1
    con0
    sslin
    ax-mp
    sstri
    eqssi
end

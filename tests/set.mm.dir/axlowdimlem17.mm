include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c2.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "wceq.mm"
include "caddc.mm"
include "cc0.mm"
include "wne.mm"
include "wss.mm"
include "uzuzle23.mm"
include "ad2antrr.mm"
include "fzss2.mm"
include "syl.mm"
include "simpr.mm"
include "sseldd.mm"
include "wn.mm"
include "fznuz.mm"
include "adantl.mm"
include "cz.mm"
include "3z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "df-3.mm"
include "fveq2i.mm"
include "eleqtri.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "necon3bi.mm"
include "axlowdimlem9.mm"
include "syl2anc.mm"
include "elfzuz.mm"
include "ad2antlr.mm"
include "eluzp1p1.mm"
include "uzss.mm"
include "ssneldd.mm"
include "eluzelz.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "axlowdimlem12.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "axlowdimlem16.mm"
include "csn.mm"
include "cxp.mm"
include "cpr.mm"
include "cun.mm"
include "fveq1i.mm"
include "cin.mm"
include "c0.mm"
include "axlowdimlem2.mm"
include "wfn.mm"
include "cr.mm"
include "wf.mm"
include "axlowdimlem4.mm"
include "ffn.mm"
include "axlowdimlem1.mm"
include "fvun2.mm"
include "mp3an12.mm"
include "mpan.mm"
include "syl5eq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cee.mm"
include "cc.mm"
include "axlowdimlem7.mm"
include "cn.mm"
include "3nn.mm"
include "nnuz.mm"
include "fzss1.mm"
include "sseli.mm"
include "fveecn.mm"
include "subid1d.mm"
include "eluzge3nn.mm"
include "2eluzge1.mm"
include "axlowdimlem10.mm"
include "syl2an.mm"
include "3eqtr4d.mm"
include "oveq12d.mm"
include "a1i.mm"
include "cle.mm"
include "eluzelre.mm"
include "eluzle.mm"
include "2re.mm"
include "3re.mm"
include "2lt3.mm"
include "ltleii.mm"
include "wi.mm"
include "letr.mm"
include "mpani.mm"
include "sylc.mm"
include "1le2.mm"
include "jctil.mm"
include "adantr.mm"
include "wb.mm"
include "2z.mm"
include "1z.mm"
include "elfz.mm"
include "mpbird.mm"
include "fzsplit.mm"
include "oveq1i.mm"
include "uneq2i.mm"
include "syl6eqr.mm"
include "fzfid.mm"
include "sylancom.mm"
include "axlowdimlem5.mm"
include "syl5eqel.mm"
include "subcld.mm"
include "sqcld.mm"
include "fsumsplit.mm"
include "sylan.mm"
include "brcgr.mm"
include "syl22anc.mm"

theorem axlowdimlem17
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let vi: setvar i
  assume axlowdimlem16.1: |- P = ( { <. 3 , -u 1 >. } u. ( ( ( 1 ... N ) \ { 3 } ) X. { 0 } ) )
  assume axlowdimlem16.2: |- Q = ( { <. ( I + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( I + 1 ) } ) X. { 0 } ) )
  assume axlowdimlem17.3: |- A = ( { <. 1 , X >. , <. 2 , Y >. } u. ( ( 3 ... N ) X. { 0 } ) )
  assume axlowdimlem17.4: |- X e. RR
  assume axlowdimlem17.5: |- Y e. RR


  assert |- ( ( N e. ( ZZ>= ` 3 ) /\ I e. ( 2 ... ( N - 1 ) ) ) -> <. P , A >. Cgr <. Q , A >. )

  proof
    cN
    c3
    cuz
    cfv
    #
    wcel
    #
    cI
    c2
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cP
    cA
    cop
    cQ
    cA
    cop
    ccgr
    wbr
    #
    c1
    cN
    cfz
    co
    #
    vi
    cv
    #
    cP
    cfv
    #
    @8
    cA
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @7
    @8
    cQ
    cfv
    #
    @10
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    wceq
    #
    @5
    c1
    c2
    cfz
    co
    #
    @12
    vi
    csu
    #
    c3
    cN
    cfz
    co
    #
    @12
    vi
    csu
    #
    caddc
    co
    @19
    @16
    vi
    csu
    #
    @21
    @16
    vi
    csu
    #
    caddc
    co
    @13
    @17
    @5
    @20
    @23
    @22
    @24
    caddc
    @5
    @19
    @12
    @16
    vi
    @5
    @8
    @19
    wcel
    #
    wa
    #
    @11
    @15
    c2
    cexp
    @26
    @9
    @14
    @10
    cmin
    @26
    @9
    cc0
    @14
    @26
    @8
    @7
    wcel
    #
    @8
    c3
    wne
    #
    @9
    cc0
    wceq
    @26
    @19
    @7
    @8
    @26
    cN
    c2
    cuz
    cfv
    #
    wcel
    #
    @19
    @7
    wss
    @1
    @30
    @4
    @25
    cN
    uzuzle23
    #
    ad2antrr
    c2
    c1
    cN
    fzss2
    syl
    @5
    @25
    simpr
    sseldd
    #
    @26
    @8
    c2
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wn
    #
    @28
    @25
    @36
    @5
    @8
    c1
    c2
    fznuz
    adantl
    #
    @35
    @8
    c3
    @8
    c3
    wceq
    @35
    c3
    @34
    wcel
    c3
    @0
    @34
    c3
    cz
    wcel
    c3
    @0
    wcel
    3z
    c3
    uzid
    ax-mp
    c3
    @33
    cuz
    df-3
    fveq2i
    eleqtri
    @8
    c3
    @34
    eleq1
    mpbiri
    necon3bi
    syl
    cP
    @8
    cN
    axlowdimlem16.1
    axlowdimlem9
    syl2anc
    @26
    @27
    @8
    cI
    c1
    caddc
    co
    #
    wne
    #
    @14
    cc0
    wceq
    @32
    @26
    @8
    @38
    cuz
    cfv
    #
    wcel
    #
    wn
    @39
    @26
    @40
    @34
    @8
    @26
    @38
    @34
    wcel
    #
    @40
    @34
    wss
    @26
    cI
    @29
    wcel
    #
    @42
    @4
    @43
    @1
    @25
    cI
    c2
    @2
    elfzuz
    ad2antlr
    c2
    cI
    eluzp1p1
    syl
    #
    @33
    @38
    uzss
    syl
    @37
    ssneldd
    @26
    @41
    @8
    @38
    @26
    @41
    @8
    @38
    wceq
    @38
    @40
    wcel
    #
    @26
    @38
    cz
    wcel
    #
    @45
    @26
    @42
    @46
    @44
    @33
    @38
    eluzelz
    syl
    @38
    uzid
    syl
    @8
    @38
    @40
    eleq1
    syl5ibrcom
    necon3bd
    mpd
    cQ
    cI
    @8
    cN
    axlowdimlem16.2
    axlowdimlem12
    syl2anc
    eqtr4d
    oveq1d
    oveq1d
    sumeq2dv
    @5
    @21
    @9
    c2
    cexp
    co
    #
    vi
    csu
    @21
    @14
    c2
    cexp
    co
    #
    vi
    csu
    @22
    @24
    cP
    cQ
    vi
    cI
    cN
    axlowdimlem16.1
    axlowdimlem16.2
    axlowdimlem16
    @5
    @21
    @12
    @47
    vi
    @5
    @8
    @21
    wcel
    #
    wa
    #
    @11
    @9
    c2
    cexp
    @50
    @11
    @9
    cc0
    cmin
    co
    @9
    @50
    @10
    cc0
    @9
    cmin
    @49
    @10
    cc0
    wceq
    @5
    @49
    @10
    @8
    @21
    cc0
    csn
    cxp
    #
    cfv
    #
    cc0
    @49
    @10
    @8
    c1
    cX
    cop
    c2
    cY
    cop
    cpr
    #
    @51
    cun
    #
    cfv
    #
    @52
    @8
    cA
    @54
    axlowdimlem17.3
    fveq1i
    @19
    @21
    cin
    c0
    wceq
    #
    @49
    @55
    @52
    wceq
    #
    cN
    axlowdimlem2
    #
    @53
    @19
    wfn
    #
    @51
    @21
    wfn
    #
    @56
    @49
    wa
    @57
    @19
    cr
    @53
    wf
    @59
    cX
    cY
    axlowdimlem17.4
    axlowdimlem17.5
    axlowdimlem4
    @19
    cr
    @53
    ffn
    ax-mp
    @21
    cr
    @51
    wf
    @60
    cN
    axlowdimlem1
    @21
    cr
    @51
    ffn
    ax-mp
    @19
    @21
    @53
    @51
    @8
    fvun2
    mp3an12
    mpan
    syl5eq
    @21
    cc0
    @8
    c0ex
    fvconst2
    eqtrd
    adantl
    #
    oveq2d
    @50
    @9
    @50
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    @27
    @9
    cc
    wcel
    #
    @1
    @63
    @4
    @49
    cP
    cN
    axlowdimlem16.1
    axlowdimlem7
    #
    ad2antrr
    @49
    @27
    @5
    @21
    @7
    @8
    c3
    c1
    cuz
    cfv
    #
    wcel
    @21
    @7
    wss
    c3
    cn
    @66
    3nn
    nnuz
    eleqtri
    c3
    c1
    cN
    fzss1
    ax-mp
    sseli
    #
    adantl
    cP
    @8
    cN
    fveecn
    #
    syl2anc
    subid1d
    eqtrd
    oveq1d
    sumeq2dv
    @5
    @21
    @16
    @48
    vi
    @50
    @15
    @14
    c2
    cexp
    @50
    @15
    @14
    cc0
    cmin
    co
    @14
    @50
    @10
    cc0
    @14
    cmin
    @61
    oveq2d
    @50
    @14
    @5
    cQ
    @62
    wcel
    #
    @27
    @14
    cc
    wcel
    #
    @49
    @1
    cN
    cn
    wcel
    cI
    c1
    @2
    cfz
    co
    #
    wcel
    @69
    @4
    cN
    eluzge3nn
    @3
    @71
    cI
    c2
    @66
    wcel
    @3
    @71
    wss
    2eluzge1
    c2
    c1
    @2
    fzss1
    ax-mp
    sseli
    cQ
    cI
    cN
    axlowdimlem16.2
    axlowdimlem10
    syl2an
    #
    @67
    cQ
    @8
    cN
    fveecn
    #
    syl2an
    subid1d
    eqtrd
    oveq1d
    sumeq2dv
    3eqtr4d
    oveq12d
    @5
    @19
    @21
    @12
    @7
    vi
    @56
    @5
    @58
    a1i
    #
    @5
    @7
    @19
    @33
    cN
    cfz
    co
    #
    cun
    #
    @19
    @21
    cun
    @5
    c2
    @7
    wcel
    #
    @7
    @76
    wceq
    @5
    @77
    c1
    c2
    cle
    wbr
    #
    c2
    cN
    cle
    wbr
    #
    wa
    #
    @1
    @80
    @4
    @1
    @79
    @78
    @1
    cN
    cr
    wcel
    #
    c3
    cN
    cle
    wbr
    #
    @79
    c3
    cN
    eluzelre
    c3
    cN
    eluzle
    @81
    c2
    c3
    cle
    wbr
    #
    @82
    @79
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    c2
    cr
    wcel
    c3
    cr
    wcel
    @81
    @83
    @82
    wa
    @79
    wi
    2re
    3re
    c2
    c3
    cN
    letr
    mp3an12
    mpani
    sylc
    1le2
    jctil
    adantr
    @5
    cN
    cz
    wcel
    #
    @77
    @80
    wb
    #
    @1
    @84
    @4
    c3
    cN
    eluzelz
    adantr
    c2
    cz
    wcel
    c1
    cz
    wcel
    @84
    @85
    2z
    1z
    c2
    c1
    cN
    elfz
    mp3an12
    syl
    mpbird
    c2
    c1
    cN
    fzsplit
    syl
    @21
    @75
    @19
    c3
    @33
    cN
    cfz
    df-3
    oveq1i
    uneq2i
    syl6eqr
    #
    @5
    c1
    cN
    fzfid
    #
    @5
    @27
    wa
    #
    @11
    @88
    @9
    @10
    @5
    @27
    @63
    @64
    @1
    @63
    @4
    @27
    @65
    ad2antrr
    @68
    sylancom
    @5
    @27
    cA
    @62
    wcel
    #
    @10
    cc
    wcel
    @1
    @89
    @4
    @27
    @1
    @30
    @89
    @31
    @30
    cA
    @54
    @62
    axlowdimlem17.3
    cX
    cY
    cN
    axlowdimlem17.4
    axlowdimlem17.5
    axlowdimlem5
    syl5eqel
    syl
    #
    ad2antrr
    cA
    @8
    cN
    fveecn
    sylancom
    #
    subcld
    sqcld
    fsumsplit
    @5
    @19
    @21
    @16
    @7
    vi
    @74
    @86
    @87
    @88
    @15
    @88
    @14
    @10
    @5
    @69
    @27
    @70
    @72
    @73
    sylan
    @91
    subcld
    sqcld
    fsumsplit
    3eqtr4d
    @5
    @63
    @89
    @69
    @89
    @6
    @18
    wb
    @1
    @63
    @4
    @65
    adantr
    @1
    @89
    @4
    @90
    adantr
    #
    @72
    @92
    cP
    cA
    cQ
    cA
    vi
    cN
    brcgr
    syl22anc
    mpbird
end

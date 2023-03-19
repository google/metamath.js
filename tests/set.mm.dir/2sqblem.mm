include "c1.mm"
include "cneg.mm"
include "clgs.mm"
include "co.mm"
include "wceq.mm"
include "c4.mm"
include "cmo.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "cz.mm"
include "wrex.mm"
include "cprime.mm"
include "wcel.mm"
include "wne.mm"
include "simpld.mm"
include "nprmdvds1.mm"
include "syl.mm"
include "wb.mm"
include "prmz.mm"
include "1z.mm"
include "dvdsnegb.mm"
include "sylancl.mm"
include "mtbid.mm"
include "cmul.mm"
include "zmulcld.mm"
include "caddc.mm"
include "zsqcl.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "simprd.mm"
include "peano2zm.mm"
include "zcnd.mm"
include "peano2zd.mm"
include "addcomd.mm"
include "cc.mm"
include "ax-1cn.mm"
include "a1i.mm"
include "ppncand.mm"
include "adddird.mm"
include "oveq1d.mm"
include "sqmuld.mm"
include "oveq12d.mm"
include "3eqtr4rd.mm"
include "3eqtrd.mm"
include "breqtrrd.mm"
include "mpbid.mm"
include "negsubdi2.mm"
include "sylancr.mm"
include "cgcd.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "zred.mm"
include "absresq.mm"
include "resqcld.mm"
include "cn.mm"
include "prmnn.mm"
include "nnred.mm"
include "cn0.mm"
include "zsqcl2.mm"
include "nn0addge2.mm"
include "exp1d.mm"
include "2z.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "1lt2.mm"
include "ltexp2a.mm"
include "syl32anc.mm"
include "eqbrtrrd.mm"
include "lelttrd.mm"
include "eqbrtrd.mm"
include "abscld.mm"
include "absge0d.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "lt2sqd.mm"
include "mpbird.mm"
include "ltnled.mm"
include "wi.mm"
include "cc0.mm"
include "sqnprm.mm"
include "abs00ad.mm"
include "eqeltrrd.mm"
include "sq0i.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "addid1d.mm"
include "sylibd.mm"
include "sylbid.mm"
include "mtod.mm"
include "wo.mm"
include "nn0abscl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "dvdsle.mm"
include "dvdsabsb.mm"
include "mtbird.mm"
include "coprm.mm"
include "eqtr3d.mm"
include "pncand.mm"
include "eqtrd.mm"
include "negeqd.mm"
include "dvdsmultr2.mm"
include "syl3anc.mm"
include "mpd.mm"
include "sq1.mm"
include "oveq2i.mm"
include "subsq.mm"
include "syl5eqr.mm"
include "dvdsadd2b.mm"
include "syl112anc.mm"
include "subneg.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rspcev.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "neg1z.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "lgsqr.mm"
include "mpbir2and.mm"
include "m1lgs.mm"

theorem 2sqblem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume 2sqb.1: |- ( ph -> ( P e. Prime /\ P =/= 2 ) )
  assume 2sqb.2: |- ( ph -> ( X e. ZZ /\ Y e. ZZ ) )
  assume 2sqb.3: |- ( ph -> P = ( ( X ^ 2 ) + ( Y ^ 2 ) ) )
  assume 2sqb.4: |- ( ph -> A e. ZZ )
  assume 2sqb.5: |- ( ph -> B e. ZZ )
  assume 2sqb.6: |- ( ph -> ( P gcd Y ) = ( ( P x. A ) + ( Y x. B ) ) )


  assert |- ( ph -> ( P mod 4 ) = 1 )

  proof
    wph
    c1
    cneg
    #
    cP
    clgs
    co
    c1
    wceq
    #
    cP
    c4
    cmo
    co
    c1
    wceq
    #
    wph
    @1
    cP
    @0
    cdvds
    wbr
    #
    wn
    #
    cP
    vx
    cv
    #
    c2
    cexp
    co
    #
    @0
    cmin
    co
    #
    cdvds
    wbr
    #
    vx
    cz
    wrex
    #
    wph
    cP
    c1
    cdvds
    wbr
    #
    @3
    wph
    cP
    cprime
    wcel
    #
    @10
    wn
    wph
    @11
    cP
    c2
    wne
    #
    2sqb.1
    simpld
    #
    cP
    nprmdvds1
    syl
    wph
    cP
    cz
    wcel
    #
    c1
    cz
    wcel
    #
    @10
    @3
    wb
    wph
    @11
    @14
    @13
    cP
    prmz
    syl
    #
    1z
    cP
    c1
    dvdsnegb
    sylancl
    mtbid
    wph
    cX
    cB
    cmul
    co
    #
    cz
    wcel
    #
    cP
    @17
    c2
    cexp
    co
    #
    @0
    cmin
    co
    #
    cdvds
    wbr
    #
    @9
    wph
    cX
    cB
    wph
    cX
    cz
    wcel
    #
    cY
    cz
    wcel
    #
    2sqb.2
    simpld
    #
    2sqb.5
    zmulcld
    #
    wph
    cP
    @19
    c1
    caddc
    co
    #
    @20
    cdvds
    wph
    cP
    @26
    cdvds
    wbr
    #
    cP
    cY
    cB
    cmul
    co
    #
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    @26
    caddc
    co
    #
    cdvds
    wbr
    #
    wph
    cP
    cP
    cB
    c2
    cexp
    co
    #
    cmul
    co
    #
    @31
    cdvds
    wph
    @14
    @33
    cz
    wcel
    #
    cP
    @34
    cdvds
    wbr
    @16
    wph
    cB
    cz
    wcel
    @35
    2sqb.5
    cB
    zsqcl
    syl
    #
    cP
    @33
    dvdsmul1
    syl2anc
    wph
    @31
    @26
    @30
    caddc
    co
    @19
    @29
    caddc
    co
    #
    @34
    wph
    @30
    @26
    wph
    @30
    wph
    @29
    cz
    wcel
    #
    @30
    cz
    wcel
    #
    wph
    @28
    cz
    wcel
    #
    @38
    wph
    cY
    cB
    wph
    @22
    @23
    2sqb.2
    simprd
    #
    2sqb.5
    zmulcld
    #
    @28
    zsqcl
    syl
    #
    @29
    peano2zm
    syl
    #
    zcnd
    wph
    @26
    wph
    @19
    wph
    @18
    @19
    cz
    wcel
    @25
    @17
    zsqcl
    syl
    #
    peano2zd
    #
    zcnd
    addcomd
    wph
    @19
    c1
    @29
    wph
    @19
    @45
    zcnd
    #
    c1
    cc
    wcel
    #
    wph
    ax-1cn
    a1i
    wph
    @29
    @43
    zcnd
    ppncand
    wph
    cX
    c2
    cexp
    co
    #
    cY
    c2
    cexp
    co
    #
    caddc
    co
    #
    @33
    cmul
    co
    @49
    @33
    cmul
    co
    #
    @50
    @33
    cmul
    co
    #
    caddc
    co
    @34
    @37
    wph
    @49
    @50
    @33
    wph
    @49
    wph
    @22
    @49
    cz
    wcel
    @24
    cX
    zsqcl
    syl
    zcnd
    #
    wph
    @50
    wph
    @23
    @50
    cz
    wcel
    @41
    cY
    zsqcl
    syl
    zcnd
    wph
    @33
    @36
    zcnd
    adddird
    wph
    cP
    @51
    @33
    cmul
    2sqb.3
    oveq1d
    wph
    @19
    @52
    @29
    @53
    caddc
    wph
    cX
    cB
    wph
    cX
    @24
    zcnd
    wph
    cB
    2sqb.5
    zcnd
    #
    sqmuld
    wph
    cY
    cB
    wph
    cY
    @41
    zcnd
    #
    @55
    sqmuld
    oveq12d
    3eqtr4rd
    3eqtrd
    breqtrrd
    wph
    @14
    @26
    cz
    wcel
    @39
    cP
    @30
    cdvds
    wbr
    @27
    @32
    wb
    @16
    @46
    @44
    wph
    cP
    @28
    c1
    caddc
    co
    #
    @28
    c1
    cmin
    co
    #
    cmul
    co
    #
    @30
    cdvds
    wph
    cP
    @58
    cdvds
    wbr
    #
    cP
    @59
    cdvds
    wbr
    #
    wph
    cP
    cP
    cA
    cmul
    co
    #
    cneg
    #
    @58
    cdvds
    wph
    cP
    @62
    cdvds
    wbr
    #
    cP
    @63
    cdvds
    wbr
    #
    wph
    @14
    cA
    cz
    wcel
    @64
    @16
    2sqb.4
    cP
    cA
    dvdsmul1
    syl2anc
    wph
    @14
    @62
    cz
    wcel
    @64
    @65
    wb
    @16
    wph
    cP
    cA
    @16
    2sqb.4
    zmulcld
    #
    cP
    @62
    dvdsnegb
    syl2anc
    mpbid
    wph
    c1
    @28
    cmin
    co
    #
    cneg
    #
    @58
    @63
    wph
    @48
    @28
    cc
    wcel
    #
    @68
    @58
    wceq
    ax-1cn
    wph
    @28
    @42
    zcnd
    #
    c1
    @28
    negsubdi2
    sylancr
    wph
    @67
    @62
    wph
    @67
    @62
    @28
    caddc
    co
    #
    @28
    cmin
    co
    @62
    wph
    c1
    @71
    @28
    cmin
    wph
    cP
    cY
    cgcd
    co
    #
    c1
    @71
    wph
    cP
    cY
    cdvds
    wbr
    #
    wn
    #
    @72
    c1
    wceq
    #
    wph
    @73
    cP
    cY
    cabs
    cfv
    #
    cdvds
    wbr
    #
    wph
    @77
    cP
    @76
    cle
    wbr
    #
    wph
    @76
    cP
    clt
    wbr
    #
    @78
    wn
    wph
    @79
    @76
    c2
    cexp
    co
    #
    cP
    c2
    cexp
    co
    #
    clt
    wbr
    wph
    @80
    @50
    @81
    clt
    wph
    cY
    cr
    wcel
    @80
    @50
    wceq
    wph
    cY
    @41
    zred
    #
    cY
    absresq
    syl
    wph
    @50
    cP
    @81
    wph
    cY
    @82
    resqcld
    #
    wph
    cP
    wph
    @11
    cP
    cn
    wcel
    #
    @13
    cP
    prmnn
    syl
    #
    nnred
    #
    wph
    cP
    @86
    resqcld
    wph
    @50
    @51
    cP
    cle
    wph
    @50
    cr
    wcel
    @49
    cn0
    wcel
    #
    @50
    @51
    cle
    wbr
    @83
    wph
    @22
    @87
    @24
    cX
    zsqcl2
    syl
    @50
    @49
    nn0addge2
    syl2anc
    2sqb.3
    breqtrrd
    wph
    cP
    c1
    cexp
    co
    #
    cP
    @81
    clt
    wph
    cP
    wph
    cP
    @16
    zcnd
    exp1d
    wph
    cP
    cr
    wcel
    @15
    c2
    cz
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    c1
    c2
    clt
    wbr
    #
    @88
    @81
    clt
    wbr
    @86
    @15
    wph
    1z
    a1i
    @89
    wph
    2z
    a1i
    wph
    cP
    c2
    cuz
    cfv
    wcel
    #
    @90
    wph
    @11
    @92
    @13
    cP
    prmuz2
    syl
    @92
    @84
    @90
    cP
    eluz2b2
    simprbi
    syl
    @91
    wph
    1lt2
    a1i
    cP
    c1
    c2
    ltexp2a
    syl32anc
    eqbrtrrd
    lelttrd
    eqbrtrd
    wph
    @76
    cP
    wph
    cY
    @56
    abscld
    #
    @86
    wph
    cY
    @56
    absge0d
    wph
    cP
    wph
    cP
    @85
    nnnn0d
    nn0ge0d
    lt2sqd
    mpbird
    wph
    @76
    cP
    @93
    wph
    cP
    @16
    zred
    ltnled
    mpbid
    wph
    @14
    @76
    cn
    wcel
    #
    @77
    @78
    wi
    @16
    wph
    @94
    @76
    cc0
    wceq
    #
    wph
    @95
    @49
    cprime
    wcel
    #
    wph
    @22
    @96
    wn
    @24
    cX
    sqnprm
    syl
    wph
    @95
    cY
    cc0
    wceq
    #
    @96
    wph
    cY
    @56
    abs00ad
    wph
    @97
    @49
    cc0
    caddc
    co
    #
    cprime
    wcel
    #
    @96
    wph
    @51
    cprime
    wcel
    @97
    @99
    wph
    cP
    @51
    cprime
    2sqb.3
    @13
    eqeltrrd
    @97
    @51
    @98
    cprime
    @97
    @50
    cc0
    @49
    caddc
    cY
    sq0i
    oveq2d
    eleq1d
    syl5ibcom
    wph
    @98
    @49
    cprime
    wph
    @49
    @54
    addid1d
    eleq1d
    sylibd
    sylbid
    mtod
    wph
    @94
    @95
    wph
    @76
    cn0
    wcel
    #
    @94
    @95
    wo
    wph
    @23
    @100
    @41
    cY
    nn0abscl
    syl
    @76
    elnn0
    sylib
    ord
    mt3d
    cP
    @76
    dvdsle
    syl2anc
    mtod
    wph
    @14
    @23
    @73
    @77
    wb
    @16
    @41
    cP
    cY
    dvdsabsb
    syl2anc
    mtbird
    wph
    @11
    @23
    @74
    @75
    wb
    @13
    @41
    cP
    cY
    coprm
    syl2anc
    mpbid
    2sqb.6
    eqtr3d
    oveq1d
    wph
    @62
    @28
    wph
    @62
    @66
    zcnd
    @70
    pncand
    eqtrd
    negeqd
    eqtr3d
    breqtrrd
    wph
    @14
    @57
    cz
    wcel
    @58
    cz
    wcel
    #
    @60
    @61
    wi
    @16
    wph
    @28
    @42
    peano2zd
    wph
    @40
    @101
    @42
    @28
    peano2zm
    syl
    cP
    @57
    @58
    dvdsmultr2
    syl3anc
    mpd
    wph
    @30
    @29
    c1
    c2
    cexp
    co
    #
    cmin
    co
    #
    @59
    @102
    c1
    @29
    cmin
    sq1
    oveq2i
    wph
    @69
    @48
    @103
    @59
    wceq
    @70
    ax-1cn
    @28
    c1
    subsq
    sylancl
    syl5eqr
    breqtrrd
    cP
    @26
    @30
    dvdsadd2b
    syl112anc
    mpbird
    wph
    @19
    cc
    wcel
    @48
    @20
    @26
    wceq
    @47
    ax-1cn
    @19
    c1
    subneg
    sylancl
    breqtrrd
    @8
    @21
    vx
    @17
    cz
    @5
    @17
    wceq
    #
    @7
    @20
    cP
    cdvds
    @104
    @6
    @19
    @0
    cmin
    @5
    @17
    c2
    cexp
    oveq1
    oveq1d
    breq2d
    rspcev
    syl2anc
    wph
    @0
    cz
    wcel
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    @1
    @4
    @9
    wa
    wb
    neg1z
    wph
    @11
    @12
    wa
    @105
    2sqb.1
    cP
    cprime
    c2
    eldifsn
    sylibr
    #
    vx
    @0
    cP
    lgsqr
    sylancr
    mpbir2and
    wph
    @105
    @1
    @2
    wb
    @106
    cP
    m1lgs
    syl
    mpbid
end

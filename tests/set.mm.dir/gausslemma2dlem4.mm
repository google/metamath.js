include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprod.mm"
include "caddc.mm"
include "cmul.mm"
include "gausslemma2dlem1.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "eldif.mm"
include "c3.mm"
include "c5.mm"
include "cuz.mm"
include "w3o.mm"
include "prm23ge5.mm"
include "eleq1.mm"
include "notbid.mm"
include "wne.mm"
include "2ex.mm"
include "snid.mm"
include "2a1i.mm"
include "necon1bd.mm"
include "a1dd.mm"
include "sylbid.mm"
include "cc0.mm"
include "c4.mm"
include "cdiv.mm"
include "cfl.mm"
include "clt.mm"
include "wbr.mm"
include "3lt4.mm"
include "breq1.mm"
include "mpbiri.mm"
include "cn0.mm"
include "cn.mm"
include "wb.mm"
include "3nn0.mm"
include "4nn.mm"
include "divfl0.mm"
include "sylancl.mm"
include "mpbid.mm"
include "syl5eq.mm"
include "c0.mm"
include "oveq2.mm"
include "adantr.mm"
include "fz10.mm"
include "syl6eq.mm"
include "prodeq1d.mm"
include "prod0.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "fzfid.mm"
include "cc.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "a1i.mm"
include "breq1d.mm"
include "oveq2d.mm"
include "ifbieq12d.mm"
include "adantl.mm"
include "simpr.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "2cnd.mm"
include "mulcld.mm"
include "eldifi.mm"
include "prmz.mm"
include "3syl.mm"
include "subcld.mm"
include "ifcld.mm"
include "fvmptd.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "fprodcl.mm"
include "mulid2d.mm"
include "eqtr2d.mm"
include "ex.mm"
include "syl.mm"
include "a1d.mm"
include "cin.mm"
include "gausslemma2dlem0d.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "cun.mm"
include "cle.mm"
include "w3a.mm"
include "cz.mm"
include "eluzelre.mm"
include "cr.mm"
include "4re.mm"
include "4ne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "crp.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "eluz2.mm"
include "4lt5.mm"
include "5re.mm"
include "zre.mm"
include "ltleletr.mm"
include "mp3an2i.mm"
include "mpani.mm"
include "3impia.mm"
include "sylbi.mm"
include "divge1.mm"
include "1zzd.mm"
include "flge.mm"
include "syl2anc.mm"
include "elnnz1.mm"
include "sylanbrc.mm"
include "oddprm.mm"
include "prmuz2.mm"
include "fldiv4lem1div2uz2.mm"
include "3jca.mm"
include "impcom.mm"
include "oveq2i.mm"
include "eleq12i.mm"
include "elfz1b.mm"
include "bitri.mm"
include "sylibr.mm"
include "fzsplit.mm"
include "fprodsplit.mm"
include "3jaoi.mm"
include "imp.mm"
include "mpcom.mm"
include "eqtrd.mm"

theorem gausslemma2dlem4
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cH: class H
  let cM: class M
  let vy: setvar y
  let vl: setvar l
  assume gausslemma2d.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2d.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2d.r: |- R = ( x e. ( 1 ... H ) |-> if ( ( x x. 2 ) < ( P / 2 ) , ( x x. 2 ) , ( P - ( x x. 2 ) ) ) )
  assume gausslemma2d.m: |- M = ( |_ ` ( P / 4 ) )

  disjoint H x
  disjoint P x
  disjoint ph x
  disjoint H k
  disjoint R k
  disjoint k ph
  disjoint M x
  disjoint k x
  disjoint M k
  disjoint P k
  disjoint H y
  disjoint x y
  disjoint R y
  disjoint ph y
  disjoint H l
  disjoint k l
  disjoint R l
  disjoint l ph
  assert |- ( ph -> ( ! ` H ) = ( prod_ k e. ( 1 ... M ) ( R ` k ) x. prod_ k e. ( ( M + 1 ) ... H ) ( R ` k ) ) )

  proof
    wph
    cH
    cfa
    cfv
    c1
    cH
    cfz
    co
    #
    vk
    cv
    #
    cR
    cfv
    #
    vk
    cprod
    #
    c1
    cM
    cfz
    co
    #
    @2
    vk
    cprod
    #
    cM
    c1
    caddc
    co
    #
    cH
    cfz
    co
    #
    @2
    vk
    cprod
    #
    cmul
    co
    #
    wph
    vx
    cP
    cR
    vk
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2dlem1
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    wph
    @3
    @9
    wceq
    #
    gausslemma2d.p
    @11
    cP
    cprime
    wcel
    #
    cP
    @10
    wcel
    #
    wn
    #
    wa
    wph
    @12
    wi
    #
    cP
    cprime
    @10
    eldif
    @13
    @15
    @16
    @13
    cP
    c2
    wceq
    #
    cP
    c3
    wceq
    #
    cP
    c5
    cuz
    cfv
    wcel
    #
    w3o
    @15
    @16
    wi
    #
    cP
    prm23ge5
    @17
    @20
    @18
    @19
    @17
    @15
    c2
    @10
    wcel
    #
    wn
    #
    @16
    @17
    @14
    @21
    cP
    c2
    @10
    eleq1
    notbid
    @17
    @22
    @12
    wph
    @17
    @21
    @3
    @9
    @21
    @17
    @3
    @9
    wne
    c2
    2ex
    snid
    2a1i
    necon1bd
    a1dd
    sylbid
    @18
    @16
    @15
    @18
    cM
    cc0
    wceq
    #
    @16
    @18
    cM
    cP
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    cc0
    gausslemma2d.m
    @18
    cP
    c4
    clt
    wbr
    #
    @25
    cc0
    wceq
    #
    @18
    @26
    c3
    c4
    clt
    wbr
    3lt4
    cP
    c3
    c4
    clt
    breq1
    mpbiri
    @18
    cP
    cn0
    wcel
    #
    c4
    cn
    wcel
    #
    @26
    @27
    wb
    @18
    @28
    c3
    cn0
    wcel
    3nn0
    cP
    c3
    cn0
    eleq1
    mpbiri
    4nn
    cP
    c4
    divfl0
    sylancl
    mpbid
    syl5eq
    @23
    wph
    @12
    @23
    wph
    wa
    #
    @9
    c1
    @3
    cmul
    co
    @3
    @30
    @5
    c1
    @8
    @3
    cmul
    @30
    @5
    c0
    @2
    vk
    cprod
    c1
    @30
    @4
    c0
    @2
    vk
    @30
    @4
    c1
    cc0
    cfz
    co
    #
    c0
    @23
    @4
    @31
    wceq
    wph
    cM
    cc0
    c1
    cfz
    oveq2
    adantr
    fz10
    syl6eq
    prodeq1d
    @2
    vk
    prod0
    syl6eq
    @30
    @7
    @0
    @2
    vk
    @30
    @6
    c1
    cH
    cfz
    @30
    @6
    cc0
    c1
    caddc
    co
    #
    c1
    @23
    @6
    @32
    wceq
    wph
    cM
    cc0
    c1
    caddc
    oveq1
    adantr
    0p1e1
    syl6eq
    oveq1d
    prodeq1d
    oveq12d
    @30
    @3
    @30
    @0
    @2
    vk
    @30
    c1
    cH
    fzfid
    wph
    @1
    @0
    wcel
    #
    @2
    cc
    wcel
    #
    @23
    wph
    @33
    wa
    #
    @2
    @1
    c2
    cmul
    co
    #
    cP
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @36
    cP
    @36
    cmin
    co
    #
    cif
    #
    cc
    @35
    vx
    @1
    vx
    cv
    #
    c2
    cmul
    co
    #
    @37
    clt
    wbr
    #
    @42
    cP
    @42
    cmin
    co
    #
    cif
    #
    @40
    @0
    cR
    cc
    cR
    vx
    @0
    @45
    cmpt
    wceq
    @35
    gausslemma2d.r
    a1i
    @41
    @1
    wceq
    #
    @45
    @40
    wceq
    @35
    @46
    @43
    @38
    @42
    @44
    @36
    @39
    @46
    @42
    @36
    @37
    clt
    @41
    @1
    c2
    cmul
    oveq1
    #
    breq1d
    @47
    @46
    @42
    @36
    cP
    cmin
    @47
    oveq2d
    ifbieq12d
    adantl
    wph
    @33
    simpr
    @35
    @38
    @36
    @39
    cc
    @33
    @36
    cc
    wcel
    wph
    @33
    @1
    c2
    @33
    @1
    @1
    c1
    cH
    elfzelz
    zcnd
    @33
    2cnd
    mulcld
    adantl
    #
    @35
    cP
    @36
    wph
    cP
    cc
    wcel
    #
    @33
    wph
    @11
    @13
    @49
    gausslemma2d.p
    cP
    cprime
    @10
    eldifi
    #
    @13
    cP
    cP
    prmz
    zcnd
    3syl
    adantr
    @48
    subcld
    ifcld
    #
    fvmptd
    @51
    eqeltrd
    #
    adantll
    fprodcl
    mulid2d
    eqtr2d
    ex
    syl
    a1d
    @19
    @16
    @15
    @19
    wph
    @12
    @19
    wph
    wa
    #
    @4
    @7
    @2
    @0
    vk
    wph
    @4
    @7
    cin
    c0
    wceq
    #
    @19
    wph
    cM
    @6
    clt
    wbr
    @54
    wph
    cM
    wph
    cM
    wph
    cP
    cM
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2dlem0d
    nn0red
    ltp1d
    c1
    cM
    @6
    cH
    fzdisj
    syl
    adantl
    @53
    cM
    @0
    wcel
    #
    @0
    @4
    @7
    cun
    wceq
    @53
    @25
    cn
    wcel
    #
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    @25
    @57
    cle
    wbr
    #
    w3a
    #
    @55
    wph
    @19
    @60
    wph
    @11
    @19
    @60
    wi
    gausslemma2d.p
    @11
    @19
    @60
    @11
    @19
    wa
    #
    @56
    @58
    @59
    @19
    @56
    @11
    @19
    @25
    cz
    wcel
    c1
    @25
    cle
    wbr
    #
    @56
    @19
    @24
    @19
    cP
    c4
    c5
    cP
    eluzelre
    #
    c4
    cr
    wcel
    #
    @19
    4re
    a1i
    c4
    cc0
    wne
    @19
    4ne0
    a1i
    redivcld
    #
    flcld
    @19
    c1
    @24
    cle
    wbr
    #
    @62
    c4
    crp
    wcel
    #
    @19
    cP
    cr
    wcel
    #
    c4
    cP
    cle
    wbr
    #
    @66
    @29
    @67
    4nn
    c4
    nnrp
    ax-mp
    @63
    @19
    c5
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    c5
    cP
    cle
    wbr
    #
    w3a
    @69
    c5
    cP
    eluz2
    @70
    @71
    @72
    @69
    @70
    @71
    wa
    #
    c4
    c5
    clt
    wbr
    #
    @72
    @69
    4lt5
    @64
    @73
    c5
    cr
    wcel
    #
    @68
    @74
    @72
    wa
    @69
    wi
    4re
    @75
    @73
    5re
    a1i
    @71
    @68
    @70
    cP
    zre
    adantl
    c4
    c5
    cP
    ltleletr
    mp3an2i
    mpani
    3impia
    sylbi
    c4
    cP
    divge1
    mp3an2i
    @19
    @24
    cr
    wcel
    c1
    cz
    wcel
    @66
    @62
    wb
    @65
    @19
    1zzd
    @24
    c1
    flge
    syl2anc
    mpbid
    @25
    elnnz1
    sylanbrc
    adantl
    @11
    @58
    @19
    cP
    oddprm
    adantr
    @61
    cP
    c2
    cuz
    cfv
    wcel
    #
    @59
    @11
    @76
    @19
    @11
    @13
    @76
    @50
    cP
    prmuz2
    syl
    adantr
    cP
    fldiv4lem1div2uz2
    syl
    3jca
    ex
    syl
    impcom
    @55
    @25
    c1
    @57
    cfz
    co
    #
    wcel
    @60
    cM
    @25
    @0
    @77
    gausslemma2d.m
    cH
    @57
    c1
    cfz
    gausslemma2d.h
    oveq2i
    eleq12i
    @57
    @25
    elfz1b
    bitri
    sylibr
    cM
    c1
    cH
    fzsplit
    syl
    @53
    c1
    cH
    fzfid
    wph
    @33
    @34
    @19
    @52
    adantll
    fprodsplit
    ex
    a1d
    3jaoi
    syl
    imp
    sylbi
    mpcom
    eqtrd
end

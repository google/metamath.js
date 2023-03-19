include "cfa.mm"
include "cfv.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "caddc.mm"
include "cmul.mm"
include "cneg.mm"
include "cexp.mm"
include "c2.mm"
include "gausslemma2dlem4.mm"
include "oveq1d.mm"
include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "crp.mm"
include "wceq.mm"
include "fzfid.mm"
include "wa.mm"
include "wral.mm"
include "gausslemma2dlem2.mm"
include "adantr.mm"
include "wi.mm"
include "rspa.mm"
include "expcom.mm"
include "adantl.mm"
include "elfzelz.mm"
include "2z.mm"
include "a1i.mm"
include "zmulcld.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "mpd.mm"
include "fprodzcl.mm"
include "cmin.mm"
include "gausslemma2dlem3.mm"
include "gausslemma2dlem0a.mm"
include "nnzd.mm"
include "zsubcl.mm"
include "syl2an.mm"
include "zred.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "nnoddn2prm.mm"
include "nnrp.mm"
include "3syl.mm"
include "w3a.mm"
include "modmulmodr.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "gausslemma2dlem5.mm"
include "oveq2d.mm"
include "neg1rr.mm"
include "gausslemma2dlem0h.mm"
include "reexpcld.mm"
include "remulcld.mm"
include "prodeq2d.mm"
include "cc.mm"
include "zcnd.mm"
include "2cn.mm"
include "fprodmul.mm"
include "clt.mm"
include "cin.mm"
include "c0.mm"
include "gausslemma2dlem0d.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "syl.mm"
include "cuz.mm"
include "cun.mm"
include "cn0.mm"
include "1zzd.mm"
include "nn0pzuz.mm"
include "syl2anc.mm"
include "cle.mm"
include "nn0zd.mm"
include "gausslemma2dlem0b.mm"
include "gausslemma2dlem0g.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzsplit2.mm"
include "fprodsplit.mm"
include "chash.mm"
include "nnnn0.mm"
include "anim1i.mm"
include "cdiv.mm"
include "nn0oddm1d2.mm"
include "biimpa.mm"
include "syl5eqel.mm"
include "fprodfac.mm"
include "cfn.mm"
include "fzfi.mm"
include "pm3.2i.mm"
include "fprodconst.mm"
include "mp1i.mm"
include "oveq12d.mm"
include "hashfz1.mm"
include "faccld.mm"
include "nncnd.mm"
include "2nn0.mm"
include "nn0expcl.mm"
include "nn0cnd.mm"
include "sylancr.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "recnd.mm"
include "mul12d.mm"
include "mulassd.mm"
include "3eqtr4d.mm"

theorem gausslemma2dlem6
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cH: class H
  let cM: class M
  let cN: class N
  let vy: setvar y
  let vk: setvar k
  let vl: setvar l
  assume gausslemma2d.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2d.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2d.r: |- R = ( x e. ( 1 ... H ) |-> if ( ( x x. 2 ) < ( P / 2 ) , ( x x. 2 ) , ( P - ( x x. 2 ) ) ) )
  assume gausslemma2d.m: |- M = ( |_ ` ( P / 4 ) )
  assume gausslemma2d.n: |- N = ( H - M )

  disjoint H x
  disjoint P x
  disjoint ph x
  disjoint M x
  disjoint H y
  disjoint x y
  disjoint R y
  disjoint ph y
  disjoint H k
  disjoint H l
  disjoint k l
  disjoint R k
  disjoint R l
  disjoint k ph
  disjoint l ph
  disjoint k x
  disjoint M k
  disjoint P k
  assert |- ( ph -> ( ( ! ` H ) mod P ) = ( ( ( ( -u 1 ^ N ) x. ( 2 ^ H ) ) x. ( ! ` H ) ) mod P ) )

  proof
    wph
    cH
    cfa
    cfv
    #
    cP
    cmo
    co
    c1
    cM
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
    cM
    c1
    caddc
    co
    #
    cH
    cfz
    co
    #
    @3
    vk
    cprod
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    @4
    @7
    cP
    cmo
    co
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    cneg
    #
    cN
    cexp
    co
    #
    c2
    cH
    cexp
    co
    #
    cmul
    co
    @0
    cmul
    co
    #
    cP
    cmo
    co
    #
    wph
    @0
    @8
    cP
    cmo
    wph
    vx
    cP
    cR
    vk
    cH
    cM
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2d.m
    gausslemma2dlem4
    oveq1d
    wph
    @4
    cz
    wcel
    #
    @7
    cr
    wcel
    #
    cP
    crp
    wcel
    #
    @9
    @12
    wceq
    wph
    @1
    @3
    vk
    wph
    c1
    cM
    fzfid
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @3
    @2
    c2
    cmul
    co
    #
    wceq
    #
    vk
    @1
    wral
    #
    @3
    cz
    wcel
    #
    wph
    @25
    @21
    wph
    vx
    cP
    cR
    vk
    cH
    cM
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2d.m
    gausslemma2dlem2
    #
    adantr
    @22
    @25
    @24
    @26
    @21
    @25
    @24
    wi
    wph
    @25
    @21
    @24
    @24
    vk
    @1
    rspa
    expcom
    adantl
    @22
    @26
    @24
    @23
    cz
    wcel
    #
    @21
    @28
    wph
    @21
    @2
    c2
    @2
    c1
    cM
    elfzelz
    c2
    cz
    wcel
    #
    @21
    2z
    a1i
    zmulcld
    adantl
    @3
    @23
    cz
    eleq1
    syl5ibrcom
    syld
    mpd
    fprodzcl
    #
    wph
    @7
    wph
    @6
    @3
    vk
    wph
    @5
    cH
    fzfid
    #
    wph
    @2
    @6
    wcel
    #
    wa
    #
    @3
    cP
    @23
    cmin
    co
    #
    wceq
    #
    vk
    @6
    wral
    #
    @26
    wph
    @36
    @32
    wph
    vx
    cP
    cR
    vk
    cH
    cM
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2d.m
    gausslemma2dlem3
    adantr
    @33
    @36
    @35
    @26
    @32
    @36
    @35
    wi
    wph
    @36
    @32
    @35
    @35
    vk
    @6
    rspa
    expcom
    adantl
    @33
    @26
    @35
    @34
    cz
    wcel
    #
    wph
    cP
    cz
    wcel
    @28
    @37
    @32
    wph
    cP
    wph
    cP
    gausslemma2d.p
    gausslemma2dlem0a
    nnzd
    @32
    @2
    c2
    @2
    @5
    cH
    elfzelz
    #
    @29
    @32
    2z
    a1i
    zmulcld
    cP
    @23
    zsubcl
    syl2an
    @3
    @34
    cz
    eleq1
    syl5ibrcom
    syld
    mpd
    fprodzcl
    zred
    wph
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    cP
    cn
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    @20
    gausslemma2d.p
    cP
    nnoddn2prm
    #
    @40
    @20
    @41
    cP
    nnrp
    adantr
    3syl
    #
    @18
    @19
    @20
    w3a
    @12
    @9
    @4
    @7
    cP
    modmulmodr
    eqcomd
    syl3anc
    wph
    @12
    @4
    @14
    @6
    @23
    vk
    cprod
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    cmul
    co
    #
    cP
    cmo
    co
    #
    @4
    @46
    cmul
    co
    #
    cP
    cmo
    co
    #
    @17
    wph
    @11
    @48
    cP
    cmo
    wph
    @10
    @47
    @4
    cmul
    wph
    vx
    cP
    cR
    vk
    cH
    cM
    cN
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2d.m
    gausslemma2d.n
    gausslemma2dlem5
    oveq2d
    oveq1d
    wph
    @18
    @46
    cr
    wcel
    @20
    @49
    @51
    wceq
    @30
    wph
    @14
    @45
    wph
    @13
    cN
    @13
    cr
    wcel
    wph
    neg1rr
    a1i
    wph
    cP
    cH
    cM
    cN
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2d.h
    gausslemma2d.n
    gausslemma2dlem0h
    reexpcld
    #
    wph
    @45
    wph
    @6
    @23
    vk
    @31
    @33
    @2
    c2
    @32
    @2
    cz
    wcel
    wph
    @38
    adantl
    @29
    @33
    2z
    a1i
    zmulcld
    fprodzcl
    #
    zred
    remulcld
    @44
    @4
    @46
    cP
    modmulmodr
    syl3anc
    wph
    @50
    @16
    cP
    cmo
    wph
    @14
    @4
    @45
    cmul
    co
    #
    cmul
    co
    @14
    @15
    @0
    cmul
    co
    #
    cmul
    co
    @50
    @16
    wph
    @54
    @55
    @14
    cmul
    wph
    @54
    @1
    @23
    vk
    cprod
    #
    @45
    cmul
    co
    #
    @55
    wph
    @4
    @56
    @45
    cmul
    wph
    @1
    @3
    @23
    vk
    @27
    prodeq2d
    oveq1d
    wph
    c1
    cH
    cfz
    co
    #
    @23
    vk
    cprod
    @58
    @2
    vk
    cprod
    #
    @58
    c2
    vk
    cprod
    #
    cmul
    co
    #
    @57
    @55
    wph
    @58
    @2
    c2
    vk
    wph
    c1
    cH
    fzfid
    #
    @2
    @58
    wcel
    #
    @2
    cc
    wcel
    wph
    @63
    @2
    @2
    c1
    cH
    elfzelz
    #
    zcnd
    adantl
    c2
    cc
    wcel
    #
    wph
    @63
    wa
    #
    2cn
    a1i
    fprodmul
    wph
    @1
    @6
    @23
    @58
    vk
    wph
    cM
    @5
    clt
    wbr
    @1
    @6
    cin
    c0
    wceq
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
    #
    nn0red
    ltp1d
    c1
    cM
    @5
    cH
    fzdisj
    syl
    wph
    @5
    c1
    cuz
    cfv
    wcel
    #
    cH
    cM
    cuz
    cfv
    wcel
    #
    @58
    @1
    @6
    cun
    wceq
    wph
    cM
    cn0
    wcel
    c1
    cz
    wcel
    @68
    @67
    wph
    1zzd
    cM
    c1
    nn0pzuz
    syl2anc
    wph
    cM
    cz
    wcel
    cH
    cz
    wcel
    cM
    cH
    cle
    wbr
    @69
    wph
    cM
    @67
    nn0zd
    wph
    cH
    wph
    cP
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2dlem0b
    nnzd
    wph
    cP
    cH
    cM
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2d.h
    gausslemma2dlem0g
    cM
    cH
    eluz2
    syl3anbrc
    cM
    c1
    cH
    fzsplit2
    syl2anc
    @62
    @66
    @23
    @63
    @28
    wph
    @63
    @2
    c2
    @64
    @29
    @63
    2z
    a1i
    zmulcld
    adantl
    zcnd
    fprodsplit
    wph
    @61
    @0
    c2
    @58
    chash
    cfv
    #
    cexp
    co
    #
    cmul
    co
    @0
    @15
    cmul
    co
    @55
    wph
    @59
    @0
    @60
    @71
    cmul
    wph
    @0
    @59
    wph
    cH
    cn0
    wcel
    #
    @0
    @59
    wceq
    wph
    @39
    cP
    cn0
    wcel
    #
    @41
    wa
    #
    @72
    gausslemma2d.p
    @39
    @42
    @74
    @43
    @40
    @73
    @41
    cP
    nnnn0
    anim1i
    syl
    @74
    cH
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cn0
    gausslemma2d.h
    @73
    @41
    @75
    cn0
    wcel
    cP
    nn0oddm1d2
    biimpa
    syl5eqel
    3syl
    #
    cH
    vk
    fprodfac
    syl
    eqcomd
    @58
    cfn
    wcel
    #
    @65
    wa
    @60
    @71
    wceq
    wph
    @77
    @65
    c1
    cH
    fzfi
    2cn
    pm3.2i
    @58
    c2
    vk
    fprodconst
    mp1i
    oveq12d
    wph
    @71
    @15
    @0
    cmul
    wph
    @70
    cH
    c2
    cexp
    wph
    @72
    @70
    cH
    wceq
    @76
    cH
    hashfz1
    syl
    oveq2d
    oveq2d
    wph
    @0
    @15
    wph
    @0
    wph
    cH
    @76
    faccld
    nncnd
    #
    wph
    c2
    cn0
    wcel
    #
    @72
    @15
    cc
    wcel
    2nn0
    @76
    @79
    @72
    wa
    @15
    c2
    cH
    nn0expcl
    nn0cnd
    sylancr
    #
    mulcomd
    3eqtrd
    3eqtr3d
    eqtrd
    oveq2d
    wph
    @4
    @14
    @45
    wph
    @4
    @30
    zcnd
    wph
    @14
    @52
    recnd
    #
    wph
    @45
    @53
    zcnd
    mul12d
    wph
    @14
    @15
    @0
    @81
    @80
    @78
    mulassd
    3eqtr4d
    oveq1d
    3eqtrd
    3eqtrd
end

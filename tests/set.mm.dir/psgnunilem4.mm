include "cword.mm"
include "wcel.mm"
include "cgsu.mm"
include "co.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "cc0.mm"
include "cn0.mm"
include "cuz.mm"
include "cfn.mm"
include "wrdfin.mm"
include "hashcl.mm"
include "3syl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "cfzo.mm"
include "wal.mm"
include "cfz.mm"
include "c0.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cc.mm"
include "neg1cn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "2a1d.mm"
include "wne.mm"
include "w3a.mm"
include "c2.mm"
include "cmin.mm"
include "wex.mm"
include "wrex.mm"
include "wn.mm"
include "simpl1.mm"
include "syl.mm"
include "simpl3l.mm"
include "eqidd.mm"
include "cn.mm"
include "simpl2.mm"
include "hashnncl.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "simpl3r.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "notbii.mm"
include "biimpi.mm"
include "adantl.mm"
include "psgnunilem3.mm"
include "iman.mm"
include "mpbir.mm"
include "df-rex.mm"
include "sylib.mm"
include "simprl.mm"
include "simprrr.mm"
include "jca.mm"
include "clt.mm"
include "wbr.mm"
include "simp3l.mm"
include "simp2.mm"
include "adantr.mm"
include "simprrl.mm"
include "cr.mm"
include "crp.mm"
include "nnred.mm"
include "2rp.mm"
include "ltsubrp.mm"
include "sylancl.mm"
include "eqbrtrd.mm"
include "elfzo0.mm"
include "syl3anbrc.mm"
include "id.mm"
include "com13.mm"
include "sylc.mm"
include "cdiv.mm"
include "a1i.mm"
include "neg1ne0.mm"
include "cz.mm"
include "2z.mm"
include "nnzd.mm"
include "expsubd.mm"
include "neg1sqe1.mm"
include "oveq2i.mm"
include "m1expcl.mm"
include "zcnd.mm"
include "div1d.mm"
include "syl5eq.mm"
include "3eqtrd.mm"
include "sylibd.mm"
include "ex.mm"
include "com23.mm"
include "alimdv.mm"
include "19.23v.mm"
include "syl6ib.mm"
include "mpid.mm"
include "3exp.mm"
include "com34.mm"
include "com12.mm"
include "impd.mm"
include "pm2.61ine.mm"
include "3adant2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "uzindi.mm"
include "mp2and.mm"

theorem psgnunilem4
  let wph: wff ph
  let cD: class D
  let cT: class T
  let cG: class G
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  assume psgnunilem4.g: |- G = ( SymGrp ` D )
  assume psgnunilem4.t: |- T = ran ( pmTrsp ` D )
  assume psgnunilem4.d: |- ( ph -> D e. V )
  assume psgnunilem4.w1: |- ( ph -> W e. Word T )
  assume psgnunilem4.w2: |- ( ph -> ( G gsum W ) = ( _I |` D ) )


  assert |- ( ph -> ( -u 1 ^ ( # ` W ) ) = 1 )

  proof
    wph
    cW
    cT
    cword
    #
    wcel
    #
    cG
    cW
    cgsu
    co
    #
    cid
    cD
    cres
    #
    wceq
    #
    c1
    cneg
    #
    cW
    chash
    cfv
    #
    cexp
    co
    #
    c1
    wceq
    #
    psgnunilem4.w1
    psgnunilem4.w2
    wph
    vw
    cv
    #
    @0
    wcel
    #
    cG
    @9
    cgsu
    co
    #
    @3
    wceq
    #
    wa
    #
    @5
    @9
    chash
    cfv
    #
    cexp
    co
    #
    c1
    wceq
    #
    wi
    #
    vx
    cv
    #
    @0
    wcel
    #
    cG
    @18
    cgsu
    co
    #
    @3
    wceq
    #
    wa
    #
    @5
    @18
    chash
    cfv
    #
    cexp
    co
    #
    c1
    wceq
    #
    wi
    #
    @1
    @4
    wa
    #
    @8
    wi
    vw
    vx
    cW
    @14
    @23
    @6
    cc0
    @0
    psgnunilem4.w1
    wph
    @6
    cn0
    cc0
    cuz
    cfv
    wph
    @1
    cW
    cfn
    wcel
    @6
    cn0
    wcel
    psgnunilem4.w1
    cT
    cW
    wrdfin
    cW
    hashcl
    3syl
    nn0uz
    syl6eleq
    wph
    @23
    cc0
    @14
    cfzo
    co
    wcel
    #
    @26
    wi
    #
    vx
    wal
    #
    @17
    @14
    cc0
    @6
    cfz
    co
    wcel
    wph
    @30
    wa
    #
    @17
    wi
    @9
    c0
    @9
    c0
    wceq
    #
    @16
    @31
    @13
    @32
    @15
    @5
    cc0
    cexp
    co
    #
    c1
    @32
    @14
    cc0
    @5
    cexp
    @32
    @14
    c0
    chash
    cfv
    cc0
    @9
    c0
    chash
    fveq2
    hash0
    syl6eq
    oveq2d
    @5
    cc
    wcel
    #
    @33
    c1
    wceq
    neg1cn
    @5
    exp0
    ax-mp
    syl6eq
    2a1d
    @9
    c0
    wne
    #
    wph
    @30
    @17
    wph
    @35
    @30
    @17
    wi
    wph
    @35
    @13
    @30
    @16
    wph
    @35
    @13
    @30
    @16
    wi
    wph
    @35
    @13
    w3a
    #
    @30
    @19
    @23
    @14
    c2
    cmin
    co
    #
    wceq
    #
    @21
    wa
    #
    wa
    #
    vx
    wex
    #
    @16
    @36
    @39
    vx
    @0
    wrex
    #
    @41
    @36
    @42
    wi
    @36
    @42
    wn
    #
    wa
    #
    wn
    @44
    vy
    cD
    cT
    cG
    @14
    cV
    @9
    psgnunilem4.g
    psgnunilem4.t
    @44
    wph
    cD
    cV
    wcel
    wph
    @35
    @13
    @43
    simpl1
    psgnunilem4.d
    syl
    @10
    @12
    wph
    @35
    @43
    simpl3l
    #
    @44
    @14
    eqidd
    @44
    @9
    cfn
    wcel
    #
    @35
    @14
    cn
    wcel
    #
    @44
    @10
    @46
    @45
    cT
    @9
    wrdfin
    #
    syl
    wph
    @35
    @13
    @43
    simpl2
    @46
    @47
    @35
    @9
    hashnncl
    biimpar
    #
    syl2anc
    @10
    @12
    wph
    @35
    @43
    simpl3r
    @43
    vy
    cv
    #
    chash
    cfv
    #
    @37
    wceq
    #
    cG
    @50
    cgsu
    co
    #
    @3
    wceq
    #
    wa
    #
    vy
    @0
    wrex
    #
    wn
    #
    @36
    @43
    @57
    @42
    @56
    @39
    @55
    vx
    vy
    @0
    @18
    @50
    wceq
    #
    @38
    @52
    @21
    @54
    @58
    @23
    @51
    @37
    @18
    @50
    chash
    fveq2
    eqeq1d
    @58
    @20
    @53
    @3
    @18
    @50
    cG
    cgsu
    oveq2
    eqeq1d
    anbi12d
    cbvrexv
    notbii
    biimpi
    adantl
    psgnunilem3
    @36
    @42
    iman
    mpbir
    @39
    vx
    @0
    df-rex
    sylib
    @36
    @30
    @40
    @16
    wi
    #
    vx
    wal
    @41
    @16
    wi
    @36
    @29
    @59
    vx
    @36
    @40
    @29
    @16
    @36
    @40
    @29
    @16
    wi
    @36
    @40
    wa
    #
    @29
    @25
    @16
    @60
    @22
    @28
    @29
    @25
    wi
    @60
    @19
    @21
    @36
    @19
    @39
    simprl
    #
    @36
    @19
    @38
    @21
    simprrr
    jca
    @60
    @23
    cn0
    wcel
    #
    @47
    @23
    @14
    clt
    wbr
    @28
    @60
    @19
    @18
    cfn
    wcel
    @62
    @61
    cT
    @18
    wrdfin
    @18
    hashcl
    3syl
    @36
    @47
    @40
    @36
    @46
    @35
    @47
    @36
    @10
    @46
    wph
    @35
    @10
    @12
    simp3l
    @48
    syl
    wph
    @35
    @13
    simp2
    @49
    syl2anc
    adantr
    #
    @60
    @23
    @37
    @14
    clt
    @36
    @19
    @38
    @21
    simprrl
    #
    @60
    @14
    cr
    wcel
    c2
    crp
    wcel
    @37
    @14
    clt
    wbr
    @60
    @14
    @63
    nnred
    2rp
    @14
    c2
    ltsubrp
    sylancl
    eqbrtrd
    @23
    @14
    elfzo0
    syl3anbrc
    @29
    @28
    @22
    @25
    @29
    id
    com13
    sylc
    @60
    @24
    @15
    c1
    @60
    @24
    @5
    @37
    cexp
    co
    @15
    @5
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @15
    @60
    @23
    @37
    @5
    cexp
    @64
    oveq2d
    @60
    @5
    @14
    c2
    @34
    @60
    neg1cn
    a1i
    @5
    cc0
    wne
    @60
    neg1ne0
    a1i
    c2
    cz
    wcel
    @60
    2z
    a1i
    @60
    @14
    @63
    nnzd
    #
    expsubd
    @60
    @66
    @15
    c1
    cdiv
    co
    @15
    @65
    c1
    @15
    cdiv
    neg1sqe1
    oveq2i
    @60
    @15
    @60
    @14
    cz
    wcel
    #
    @15
    cc
    wcel
    @67
    @68
    @15
    @14
    m1expcl
    zcnd
    syl
    div1d
    syl5eq
    3eqtrd
    eqeq1d
    sylibd
    ex
    com23
    alimdv
    @40
    @16
    vx
    19.23v
    syl6ib
    mpid
    3exp
    com34
    com12
    impd
    pm2.61ine
    3adant2
    @9
    @18
    wceq
    #
    @13
    @22
    @16
    @25
    @69
    @10
    @19
    @12
    @21
    @9
    @18
    @0
    eleq1
    @69
    @11
    @20
    @3
    @9
    @18
    cG
    cgsu
    oveq2
    eqeq1d
    anbi12d
    @69
    @15
    @24
    c1
    @69
    @14
    @23
    @5
    cexp
    @9
    @18
    chash
    fveq2
    #
    oveq2d
    eqeq1d
    imbi12d
    @9
    cW
    wceq
    #
    @13
    @27
    @16
    @8
    @71
    @10
    @1
    @12
    @4
    @9
    cW
    @0
    eleq1
    @71
    @11
    @2
    @3
    @9
    cW
    cG
    cgsu
    oveq2
    eqeq1d
    anbi12d
    @71
    @15
    @7
    c1
    @71
    @14
    @6
    @5
    cexp
    @9
    cW
    chash
    fveq2
    #
    oveq2d
    eqeq1d
    imbi12d
    @70
    @72
    uzindi
    mp2and
end

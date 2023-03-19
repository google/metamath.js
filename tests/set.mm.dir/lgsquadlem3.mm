include "clgs.mm"
include "co.mm"
include "cmul.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "copab.mm"
include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "caddc.mm"
include "necomd.mm"
include "weq.mm"
include "wb.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "ancom.mm"
include "syl6bb.mm"
include "oveq1.mm"
include "breqan12d.mm"
include "anbi12d.mm"
include "ancoms.mm"
include "cbvopabv.mm"
include "lgsquadlem2.mm"
include "cen.mm"
include "wceq.mm"
include "ccnv.mm"
include "wrel.mm"
include "cfn.mm"
include "relopab.mm"
include "cxp.mm"
include "wss.mm"
include "fzfid.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "opabssxp.mm"
include "ssfi.mm"
include "sylancl.mm"
include "cnven.mm"
include "sylancr.mm"
include "cnvopab.mm"
include "syl6breq.mm"
include "hasheni.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "oveq12d.mm"
include "cc.mm"
include "neg1cn.mm"
include "a1i.mm"
include "cn0.mm"
include "eqsstri.mm"
include "hashcl.mm"
include "expaddd.mm"
include "cun.mm"
include "wo.mm"
include "wne.mm"
include "cdvds.mm"
include "wn.mm"
include "cn.mm"
include "cmin.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "eldifad.mm"
include "adantr.mm"
include "prmnn.mm"
include "cuz.mm"
include "cz.mm"
include "cle.mm"
include "cdiv.mm"
include "cdif.mm"
include "oddprm.mm"
include "syl5eqel.mm"
include "nnzd.mm"
include "prmz.mm"
include "peano2zm.mm"
include "nnred.mm"
include "zred.mm"
include "crp.mm"
include "prmuz2.mm"
include "uz2m1nn.mm"
include "nnrpd.mm"
include "rphalflt.mm"
include "syl5eqbr.mm"
include "ltled.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "simprr.mm"
include "sseldd.mm"
include "fzm1ndvds.mm"
include "cgcd.mm"
include "prmrp.mm"
include "mpbird.mm"
include "wi.mm"
include "elfzelz.mm"
include "ad2antll.mm"
include "coprmdvds.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "mtod.mm"
include "nncnd.mm"
include "elfznn.mm"
include "mulcomd.mm"
include "breq2d.mm"
include "mtbid.mm"
include "ad2antrl.mm"
include "dvdsmul2.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "nnmulcld.mm"
include "lttri2d.mm"
include "mpbid.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "syl6rbb.mm"
include "opabbidv.mm"
include "unopab.mm"
include "uneq2i.mm"
include "andi.mm"
include "opabbii.mm"
include "3eqtr4i.mm"
include "df-xp.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "cin.mm"
include "c0.mm"
include "inopab.mm"
include "ineq2i.mm"
include "anandi.mm"
include "wex.mm"
include "cr.mm"
include "ltnsym2.mm"
include "imnan.mm"
include "sylib.mm"
include "nexdv.mm"
include "opabn0.mm"
include "necon1bbii.mm"
include "syl5eq.mm"
include "hashun.mm"
include "hashxp.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "3eqtr2d.mm"

theorem lgsquadlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cM: class M
  let cN: class N
  let vk: setvar k
  let cG: class G
  let cL: class L
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cY: class Y
  let cR: class R
  assume lgseisen.1: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume lgseisen.2: |- ( ph -> Q e. ( Prime \ { 2 } ) )
  assume lgseisen.3: |- ( ph -> P =/= Q )
  assume lgsquad.4: |- M = ( ( P - 1 ) / 2 )
  assume lgsquad.5: |- N = ( ( Q - 1 ) / 2 )
  assume lgsquad.6: |- S = { <. x , y >. | ( ( x e. ( 1 ... M ) /\ y e. ( 1 ... N ) ) /\ ( y x. P ) < ( x x. Q ) ) }

  disjoint x y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint M y
  disjoint N x
  disjoint N y
  disjoint Q x
  disjoint Q y
  disjoint S x
  disjoint M x
  disjoint S y
  disjoint k x
  disjoint G k
  disjoint G x
  disjoint L k
  disjoint L x
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint P k
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint P n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint P u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint P w
  disjoint x z
  disjoint y z
  disjoint P z
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph z
  disjoint M n
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M z
  disjoint N u
  disjoint N w
  disjoint N z
  disjoint Q k
  disjoint Q u
  disjoint Q w
  disjoint Q z
  disjoint Y k
  disjoint Y x
  disjoint R k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S z
  assert |- ( ph -> ( ( P /L Q ) x. ( Q /L P ) ) = ( -u 1 ^ ( M x. N ) ) )

  proof
    wph
    cP
    cQ
    clgs
    co
    #
    cQ
    cP
    clgs
    co
    #
    cmul
    co
    c1
    cneg
    #
    vx
    cv
    #
    c1
    cM
    cfz
    co
    #
    wcel
    #
    vy
    cv
    #
    c1
    cN
    cfz
    co
    #
    wcel
    #
    wa
    #
    @3
    cQ
    cmul
    co
    #
    @6
    cP
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    chash
    cfv
    #
    cexp
    co
    #
    @2
    cS
    chash
    cfv
    #
    cexp
    co
    #
    cmul
    co
    @2
    @15
    @17
    caddc
    co
    #
    cexp
    co
    @2
    cM
    cN
    cmul
    co
    #
    cexp
    co
    wph
    @0
    @16
    @1
    @18
    cmul
    wph
    @0
    @2
    @13
    vy
    vx
    copab
    #
    chash
    cfv
    #
    cexp
    co
    @16
    wph
    vw
    vz
    cQ
    cP
    @21
    cN
    cM
    lgseisen.2
    lgseisen.1
    wph
    cP
    cQ
    lgseisen.3
    necomd
    #
    lgsquad.5
    lgsquad.4
    @13
    vw
    cv
    #
    @7
    wcel
    #
    vz
    cv
    #
    @4
    wcel
    #
    wa
    #
    @26
    cQ
    cmul
    co
    #
    @24
    cP
    cmul
    co
    #
    clt
    wbr
    #
    wa
    #
    vy
    vx
    vw
    vz
    vx
    vz
    weq
    #
    vy
    vw
    weq
    #
    @13
    @32
    wb
    @33
    @34
    wa
    #
    @9
    @28
    @12
    @31
    @35
    @9
    @27
    @25
    wa
    @28
    @33
    @5
    @27
    @34
    @8
    @25
    @3
    @26
    @4
    eleq1
    @6
    @24
    @7
    eleq1
    bi2anan9
    @27
    @25
    ancom
    syl6bb
    @33
    @34
    @10
    @29
    @11
    @30
    clt
    @3
    @26
    cQ
    cmul
    oveq1
    @6
    @24
    cP
    cmul
    oveq1
    breqan12d
    anbi12d
    ancoms
    cbvopabv
    lgsquadlem2
    wph
    @15
    @22
    @2
    cexp
    wph
    @14
    @21
    cen
    wbr
    @15
    @22
    wceq
    wph
    @14
    @14
    ccnv
    #
    @21
    cen
    wph
    @14
    wrel
    @14
    cfn
    wcel
    #
    @14
    @36
    cen
    wbr
    @13
    vx
    vy
    relopab
    wph
    @4
    @7
    cxp
    #
    cfn
    wcel
    #
    @14
    @38
    wss
    @37
    wph
    @4
    cfn
    wcel
    #
    @7
    cfn
    wcel
    #
    @39
    wph
    c1
    cM
    fzfid
    #
    wph
    c1
    cN
    fzfid
    #
    @4
    @7
    xpfi
    syl2anc
    #
    @12
    vx
    vy
    @4
    @7
    opabssxp
    @38
    @14
    ssfi
    sylancl
    #
    @14
    cfn
    cnven
    sylancr
    @13
    vx
    vy
    cnvopab
    syl6breq
    @14
    @21
    hasheni
    syl
    oveq2d
    eqtr4d
    wph
    vx
    vy
    cP
    cQ
    cS
    cM
    cN
    lgseisen.1
    lgseisen.2
    lgseisen.3
    lgsquad.4
    lgsquad.5
    lgsquad.6
    lgsquadlem2
    oveq12d
    wph
    @2
    @15
    @17
    @2
    cc
    wcel
    wph
    neg1cn
    a1i
    wph
    cS
    cfn
    wcel
    #
    @17
    cn0
    wcel
    wph
    @39
    cS
    @38
    wss
    @46
    @44
    cS
    @9
    @11
    @10
    clt
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    @38
    lgsquad.6
    @47
    vx
    vy
    @4
    @7
    opabssxp
    eqsstri
    @38
    cS
    ssfi
    sylancl
    #
    cS
    hashcl
    syl
    wph
    @37
    @15
    cn0
    wcel
    @45
    @14
    hashcl
    syl
    expaddd
    wph
    @19
    @20
    @2
    cexp
    wph
    @14
    cS
    cun
    #
    chash
    cfv
    #
    @38
    chash
    cfv
    #
    @19
    @20
    wph
    @51
    @38
    chash
    wph
    @9
    @12
    @47
    wo
    #
    wa
    #
    vx
    vy
    copab
    #
    @9
    vx
    vy
    copab
    @51
    @38
    wph
    @55
    @9
    vx
    vy
    wph
    @9
    @54
    @9
    wa
    @55
    wph
    @9
    @54
    wph
    @9
    @54
    wph
    @9
    wa
    #
    @10
    @11
    wne
    #
    @54
    @57
    cQ
    @11
    cdvds
    wbr
    #
    wn
    @58
    @57
    cQ
    cP
    @6
    cmul
    co
    #
    cdvds
    wbr
    #
    @59
    @57
    @61
    cQ
    @6
    cdvds
    wbr
    #
    @57
    cQ
    cn
    wcel
    #
    @6
    c1
    cQ
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    @62
    wn
    @57
    cQ
    cprime
    wcel
    #
    @63
    wph
    @66
    @9
    wph
    cQ
    cprime
    c2
    csn
    #
    lgseisen.2
    eldifad
    adantr
    #
    cQ
    prmnn
    syl
    #
    @57
    @7
    @65
    @6
    @57
    @64
    cN
    cuz
    cfv
    wcel
    #
    @7
    @65
    wss
    @57
    cN
    cz
    wcel
    @64
    cz
    wcel
    #
    cN
    @64
    cle
    wbr
    @70
    @57
    cN
    wph
    cN
    cn
    wcel
    @9
    wph
    cN
    @64
    c2
    cdiv
    co
    #
    cn
    lgsquad.5
    wph
    cQ
    cprime
    @67
    cdif
    #
    wcel
    @72
    cn
    wcel
    lgseisen.2
    cQ
    oddprm
    syl
    syl5eqel
    #
    adantr
    #
    nnzd
    @57
    cQ
    cz
    wcel
    #
    @71
    @57
    @66
    @76
    @68
    cQ
    prmz
    syl
    #
    cQ
    peano2zm
    syl
    #
    @57
    cN
    @64
    @57
    cN
    @75
    nnred
    @57
    @64
    @78
    zred
    @57
    cN
    @72
    @64
    clt
    lgsquad.5
    @57
    @64
    crp
    wcel
    @72
    @64
    clt
    wbr
    @57
    @64
    @57
    cQ
    c2
    cuz
    cfv
    wcel
    #
    @64
    cn
    wcel
    @57
    @66
    @79
    @68
    cQ
    prmuz2
    syl
    cQ
    uz2m1nn
    syl
    nnrpd
    @64
    rphalflt
    syl
    syl5eqbr
    ltled
    cN
    @64
    eluz2
    syl3anbrc
    cN
    c1
    @64
    fzss2
    syl
    wph
    @5
    @8
    simprr
    sseldd
    cQ
    @6
    fzm1ndvds
    syl2anc
    @57
    @61
    cQ
    cP
    cgcd
    co
    c1
    wceq
    #
    @62
    @57
    @80
    cQ
    cP
    wne
    #
    wph
    @81
    @9
    @23
    adantr
    @57
    @66
    cP
    cprime
    wcel
    #
    @80
    @81
    wb
    @68
    wph
    @82
    @9
    wph
    cP
    cprime
    @67
    lgseisen.1
    eldifad
    adantr
    #
    cQ
    cP
    prmrp
    syl2anc
    mpbird
    @57
    @76
    cP
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @61
    @80
    wa
    @62
    wi
    @77
    @57
    @82
    @84
    @83
    cP
    prmz
    syl
    @8
    @85
    wph
    @5
    @6
    c1
    cN
    elfzelz
    ad2antll
    cQ
    cP
    @6
    coprmdvds
    syl3anc
    mpan2d
    mtod
    @57
    @60
    @11
    cQ
    cdvds
    @57
    cP
    @6
    @57
    cP
    @57
    @82
    cP
    cn
    wcel
    @83
    cP
    prmnn
    syl
    #
    nncnd
    @57
    @6
    @8
    @6
    cn
    wcel
    wph
    @5
    @6
    cN
    elfznn
    ad2antll
    #
    nncnd
    mulcomd
    breq2d
    mtbid
    @57
    @59
    @10
    @11
    @57
    cQ
    @10
    cdvds
    wbr
    #
    @10
    @11
    wceq
    @59
    @57
    @3
    cz
    wcel
    #
    @76
    @88
    @5
    @89
    wph
    @8
    @3
    c1
    cM
    elfzelz
    ad2antrl
    @77
    @3
    cQ
    dvdsmul2
    syl2anc
    @10
    @11
    cQ
    cdvds
    breq2
    syl5ibcom
    necon3bd
    mpd
    @57
    @10
    @11
    @57
    @10
    @57
    @3
    cQ
    @5
    @3
    cn
    wcel
    wph
    @8
    @3
    cM
    elfznn
    ad2antrl
    @69
    nnmulcld
    nnred
    #
    @57
    @11
    @57
    @6
    cP
    @87
    @86
    nnmulcld
    nnred
    #
    lttri2d
    mpbid
    ex
    pm4.71rd
    @54
    @9
    ancom
    syl6rbb
    opabbidv
    @14
    @49
    cun
    @13
    @48
    wo
    #
    vx
    vy
    copab
    @51
    @56
    @13
    @48
    vx
    vy
    unopab
    cS
    @49
    @14
    lgsquad.6
    uneq2i
    @55
    @92
    vx
    vy
    @9
    @12
    @47
    andi
    opabbii
    3eqtr4i
    vx
    vy
    @4
    @7
    df-xp
    3eqtr4g
    fveq2d
    wph
    @37
    @46
    @14
    cS
    cin
    #
    c0
    wceq
    @52
    @19
    wceq
    @45
    @50
    wph
    @93
    @9
    @12
    @47
    wa
    #
    wa
    #
    vx
    vy
    copab
    #
    c0
    @14
    @49
    cin
    @13
    @48
    wa
    #
    vx
    vy
    copab
    @93
    @96
    @13
    @48
    vx
    vy
    inopab
    cS
    @49
    @14
    lgsquad.6
    ineq2i
    @95
    @97
    vx
    vy
    @9
    @12
    @47
    anandi
    opabbii
    3eqtr4i
    wph
    @95
    vy
    wex
    #
    vx
    wex
    #
    wn
    @96
    c0
    wceq
    wph
    @98
    vx
    wph
    @95
    vy
    wph
    @9
    @94
    wn
    #
    wi
    @95
    wn
    wph
    @9
    @100
    @57
    @10
    cr
    wcel
    @11
    cr
    wcel
    @100
    @90
    @91
    @10
    @11
    ltnsym2
    syl2anc
    ex
    @9
    @94
    imnan
    sylib
    nexdv
    nexdv
    @99
    @96
    c0
    @95
    vx
    vy
    opabn0
    necon1bbii
    sylib
    syl5eq
    @14
    cS
    hashun
    syl3anc
    wph
    @53
    @4
    chash
    cfv
    #
    @7
    chash
    cfv
    #
    cmul
    co
    #
    @20
    wph
    @40
    @41
    @53
    @103
    wceq
    @42
    @43
    @4
    @7
    hashxp
    syl2anc
    wph
    @101
    cM
    @102
    cN
    cmul
    wph
    cM
    cn0
    wcel
    @101
    cM
    wceq
    wph
    cM
    wph
    cM
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cn
    lgsquad.4
    wph
    cP
    @73
    wcel
    @104
    cn
    wcel
    lgseisen.1
    cP
    oddprm
    syl
    syl5eqel
    nnnn0d
    cM
    hashfz1
    syl
    wph
    cN
    cn0
    wcel
    @102
    cN
    wceq
    wph
    cN
    @74
    nnnn0d
    cN
    hashfz1
    syl
    oveq12d
    eqtrd
    3eqtr3d
    oveq2d
    3eqtr2d
end

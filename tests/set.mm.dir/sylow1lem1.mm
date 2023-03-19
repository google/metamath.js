include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "cpc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "cexp.mm"
include "cbc.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "cfn.mm"
include "cz.mm"
include "cprime.mm"
include "prmnn.mm"
include "syl.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "hashbc.mm"
include "syl2anc.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "cc0.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "wi.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "cgrp.mm"
include "grpbn0.mm"
include "wb.mm"
include "hasheq0.mm"
include "necon3bbid.mm"
include "mpbird.mm"
include "cn0.mm"
include "wo.mm"
include "hashcl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "dvdsle.mm"
include "mpd.mm"
include "cuz.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "bccl2.mm"
include "eqeltrrd.mm"
include "c1.mm"
include "cdiv.mm"
include "cmul.mm"
include "caddc.mm"
include "nnuz.mm"
include "1zzd.mm"
include "fzsubel.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "bcp1nk.mm"
include "cc.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "nncnd.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "divne0d.mm"
include "pcmul.mm"
include "syl122anc.mm"
include "1cnd.mm"
include "npncand.mm"
include "oveq1d.mm"
include "clt.mm"
include "nnred.mm"
include "ltm1d.mm"
include "nnm1nn0.mm"
include "breq1.mm"
include "bcxmaslem1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "znn0sub.mm"
include "0nn0.mm"
include "nn0addcl.mm"
include "bcn0.mm"
include "pc1.mm"
include "eqtrd.mm"
include "a1d.mm"
include "wa.mm"
include "cr.mm"
include "nn0re.mm"
include "ad2antrl.mm"
include "nn0p1nn.mm"
include "adantr.mm"
include "ltp1d.mm"
include "simprr.mm"
include "lttrd.mm"
include "expr.mm"
include "imim1d.mm"
include "oveq1.mm"
include "nn0cn.mm"
include "addassd.mm"
include "nn0addge2.mm"
include "simprl.mm"
include "nn0addcld.mm"
include "eqtr3d.mm"
include "cq.mm"
include "nnq.mm"
include "peano2zd.mm"
include "znq.mm"
include "crp.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "syl2an.mm"
include "rpne0d.mm"
include "pcqmul.mm"
include "pcdiv.mm"
include "syl121anc.mm"
include "addcomd.mm"
include "simpr.mm"
include "addid1d.mm"
include "eqtr2d.mm"
include "ad2antrr.mm"
include "zq.mm"
include "pccld.mm"
include "nn0red.mm"
include "neneqd.mm"
include "pcdvdsb.mm"
include "sylbid.mm"
include "lenltd.mm"
include "3imtr3d.mm"
include "mt4d.mm"
include "dvdssubr.mm"
include "ltletrd.mm"
include "pcadd2.mm"
include "pm2.61dane.mm"
include "eqtr4d.mm"
include "eqeltrd.mm"
include "subeq0bd.mm"
include "00id.mm"
include "syl6req.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "a2d.mm"
include "syld.mm"
include "expcom.mm"
include "nn0ind.mm"
include "mpcom.mm"
include "pcid.mm"
include "zsubcld.mm"
include "zcnd.mm"
include "addid2d.mm"
include "3eqtrd.mm"
include "jca.mm"

theorem sylow1lem1
  let wph: wff ph
  let cP: class P
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cN: class N
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vg: setvar g
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vh: setvar h
  let cH: class H
  let vw: setvar w
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  let c.sm: class .~
  let c.po: class .(+)
  assume sylow1.x: |- X = ( Base ` G )
  assume sylow1.g: |- ( ph -> G e. Grp )
  assume sylow1.f: |- ( ph -> X e. Fin )
  assume sylow1.p: |- ( ph -> P e. Prime )
  assume sylow1.n: |- ( ph -> N e. NN0 )
  assume sylow1.d: |- ( ph -> ( P ^ N ) || ( # ` X ) )
  assume sylow1lem.a: |- .+ = ( +g ` G )
  assume sylow1lem.s: |- S = { s e. ~P X | ( # ` s ) = ( P ^ N ) }

  disjoint N s
  disjoint X s
  disjoint .+ s
  disjoint G s
  disjoint P s
  disjoint a b
  disjoint a c
  disjoint a g
  disjoint a s
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint B a
  disjoint b c
  disjoint b g
  disjoint b s
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint c g
  disjoint c s
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint g s
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint a h
  disjoint H a
  disjoint b h
  disjoint H b
  disjoint c h
  disjoint H c
  disjoint g h
  disjoint H g
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint a w
  disjoint S a
  disjoint b w
  disjoint S b
  disjoint c w
  disjoint S c
  disjoint g w
  disjoint S g
  disjoint u w
  disjoint S u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint N a
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint N b
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g v
  disjoint N g
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h z
  disjoint N h
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  disjoint s t
  disjoint s v
  disjoint s w
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint N t
  disjoint u v
  disjoint N u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint X a
  disjoint X b
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint X c
  disjoint X g
  disjoint X h
  disjoint X k
  disjoint X n
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint .+ b
  disjoint .+ c
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .~ a
  disjoint .~ w
  disjoint .~ z
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) c
  disjoint .(+) g
  disjoint .(+) u
  disjoint .(+) w
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint P a
  disjoint P b
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P n
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( ( # ` S ) e. NN /\ ( P pCnt ( # ` S ) ) = ( ( P pCnt ( # ` X ) ) - N ) ) )

  proof
    wph
    cS
    chash
    cfv
    #
    cn
    wcel
    cP
    @0
    cpc
    co
    #
    cP
    cX
    chash
    cfv
    #
    cpc
    co
    #
    cN
    cmin
    co
    #
    wceq
    wph
    @2
    cP
    cN
    cexp
    co
    #
    cbc
    co
    #
    @0
    cn
    wph
    @6
    vs
    cv
    chash
    cfv
    @5
    wceq
    vs
    cX
    cpw
    crab
    #
    chash
    cfv
    #
    @0
    wph
    cX
    cfn
    wcel
    #
    @5
    cz
    wcel
    #
    @6
    @8
    wceq
    sylow1.f
    wph
    @5
    wph
    cP
    cN
    wph
    cP
    cprime
    wcel
    #
    cP
    cn
    wcel
    sylow1.p
    cP
    prmnn
    syl
    sylow1.n
    nnexpcld
    #
    nnzd
    #
    vs
    cX
    @5
    hashbc
    syl2anc
    cS
    @7
    chash
    sylow1lem.s
    fveq2i
    syl6eqr
    #
    wph
    @5
    cc0
    @2
    cfz
    co
    wcel
    #
    @6
    cn
    wcel
    wph
    @15
    @5
    @2
    cle
    wbr
    #
    wph
    @5
    @2
    cdvds
    wbr
    #
    @16
    sylow1.d
    wph
    @10
    @2
    cn
    wcel
    #
    @17
    @16
    wi
    @13
    wph
    @18
    @2
    cc0
    wceq
    #
    wph
    @19
    wn
    cX
    c0
    wne
    #
    wph
    cG
    cgrp
    wcel
    @20
    sylow1.g
    cX
    cG
    sylow1.x
    grpbn0
    syl
    wph
    @19
    cX
    c0
    wph
    @9
    @19
    cX
    c0
    wceq
    wb
    sylow1.f
    cX
    cfn
    hasheq0
    syl
    necon3bbid
    mpbird
    wph
    @18
    @19
    wph
    @2
    cn0
    wcel
    #
    @18
    @19
    wo
    wph
    @9
    @21
    sylow1.f
    cX
    hashcl
    syl
    #
    @2
    elnn0
    sylib
    ord
    mt3d
    #
    @5
    @2
    dvdsle
    syl2anc
    mpd
    #
    wph
    @5
    cc0
    cuz
    cfv
    #
    wcel
    @2
    cz
    wcel
    #
    @15
    @16
    wb
    wph
    @5
    cn0
    @25
    wph
    @5
    @12
    nnnn0d
    nn0uz
    syl6eleq
    wph
    @2
    @22
    nn0zd
    #
    @5
    cc0
    @2
    elfz5
    syl2anc
    mpbird
    @5
    @2
    bccl2
    syl
    eqeltrrd
    wph
    cP
    @6
    cpc
    co
    cP
    @2
    c1
    cmin
    co
    #
    @5
    c1
    cmin
    co
    #
    cbc
    co
    #
    @2
    @5
    cdiv
    co
    #
    cmul
    co
    #
    cpc
    co
    #
    @1
    @4
    wph
    @6
    @32
    cP
    cpc
    wph
    @28
    c1
    caddc
    co
    #
    @29
    c1
    caddc
    co
    #
    cbc
    co
    #
    @30
    @34
    @35
    cdiv
    co
    #
    cmul
    co
    #
    @6
    @32
    wph
    @29
    cc0
    @28
    cfz
    co
    #
    wcel
    #
    @36
    @38
    wceq
    wph
    @29
    c1
    c1
    cmin
    co
    #
    @28
    cfz
    co
    #
    @39
    wph
    @5
    c1
    @2
    cfz
    co
    wcel
    #
    @29
    @42
    wcel
    #
    wph
    @43
    @16
    @24
    wph
    @5
    c1
    cuz
    cfv
    #
    wcel
    @26
    @43
    @16
    wb
    wph
    @5
    cn
    @45
    @12
    nnuz
    syl6eleq
    @27
    @5
    c1
    @2
    elfz5
    syl2anc
    mpbird
    wph
    c1
    cz
    wcel
    #
    @26
    @10
    @46
    @43
    @44
    wb
    wph
    1zzd
    #
    @27
    @13
    @47
    @5
    c1
    c1
    @2
    fzsubel
    syl22anc
    mpbid
    @41
    cc0
    @28
    cfz
    1m1e0
    oveq1i
    syl6eleq
    #
    @29
    @28
    bcp1nk
    syl
    wph
    @34
    @2
    @35
    @5
    cbc
    wph
    @2
    cc
    wcel
    c1
    cc
    wcel
    #
    @34
    @2
    wceq
    wph
    @2
    @22
    nn0cnd
    #
    ax-1cn
    @2
    c1
    npcan
    sylancl
    #
    wph
    @5
    cc
    wcel
    @49
    @35
    @5
    wceq
    wph
    @5
    @12
    nncnd
    #
    ax-1cn
    @5
    c1
    npcan
    sylancl
    #
    oveq12d
    wph
    @37
    @31
    @30
    cmul
    wph
    @34
    @2
    @35
    @5
    cdiv
    @51
    @53
    oveq12d
    oveq2d
    3eqtr3d
    oveq2d
    wph
    @6
    @0
    cP
    cpc
    @14
    oveq2d
    wph
    @33
    cP
    @30
    cpc
    co
    #
    cP
    @31
    cpc
    co
    #
    caddc
    co
    #
    cc0
    @4
    caddc
    co
    @4
    wph
    @11
    @30
    cz
    wcel
    @30
    cc0
    wne
    @31
    cz
    wcel
    #
    @31
    cc0
    wne
    @33
    @56
    wceq
    sylow1.p
    wph
    @30
    wph
    @40
    @30
    cn
    wcel
    @48
    @29
    @28
    bccl2
    syl
    #
    nnzd
    wph
    @30
    @58
    nnne0d
    wph
    @17
    @57
    sylow1.d
    wph
    @10
    @5
    cc0
    wne
    @26
    @17
    @57
    wb
    @13
    wph
    @5
    @12
    nnne0d
    #
    @27
    @5
    @2
    dvdsval2
    syl3anc
    mpbid
    wph
    @2
    @5
    @50
    @52
    wph
    @2
    @23
    nnne0d
    #
    @59
    divne0d
    @30
    @31
    cP
    pcmul
    syl122anc
    wph
    @54
    cc0
    @55
    @4
    caddc
    wph
    cP
    @2
    @5
    cmin
    co
    #
    @29
    caddc
    co
    #
    @29
    cbc
    co
    #
    cpc
    co
    #
    @54
    cc0
    wph
    @63
    @30
    cP
    cpc
    wph
    @62
    @28
    @29
    cbc
    wph
    @2
    @5
    c1
    @50
    @52
    wph
    1cnd
    npncand
    oveq1d
    oveq2d
    wph
    @29
    @5
    clt
    wbr
    #
    @64
    cc0
    wceq
    #
    wph
    @5
    wph
    @5
    @12
    nnred
    ltm1d
    @29
    cn0
    wcel
    #
    wph
    @65
    @66
    wi
    #
    wph
    @5
    cn
    wcel
    #
    @67
    @12
    @5
    nnm1nn0
    syl
    wph
    vx
    cv
    #
    @5
    clt
    wbr
    #
    cP
    @61
    @70
    caddc
    co
    @70
    cbc
    co
    #
    cpc
    co
    #
    cc0
    wceq
    #
    wi
    #
    wi
    wph
    cc0
    @5
    clt
    wbr
    #
    cP
    @61
    cc0
    caddc
    co
    #
    cc0
    cbc
    co
    #
    cpc
    co
    #
    cc0
    wceq
    #
    wi
    #
    wi
    wph
    vn
    cv
    #
    @5
    clt
    wbr
    #
    cP
    @61
    @82
    caddc
    co
    #
    @82
    cbc
    co
    #
    cpc
    co
    #
    cc0
    wceq
    #
    wi
    #
    wi
    wph
    @82
    c1
    caddc
    co
    #
    @5
    clt
    wbr
    #
    cP
    @61
    @89
    caddc
    co
    #
    @89
    cbc
    co
    #
    cpc
    co
    #
    cc0
    wceq
    #
    wi
    #
    wi
    wph
    @68
    wi
    vx
    vn
    @29
    @70
    cc0
    wceq
    #
    @75
    @81
    wph
    @96
    @71
    @76
    @74
    @80
    @70
    cc0
    @5
    clt
    breq1
    @96
    @73
    @79
    cc0
    @96
    @72
    @78
    cP
    cpc
    @70
    cc0
    @61
    bcxmaslem1
    oveq2d
    eqeq1d
    imbi12d
    imbi2d
    @70
    @82
    wceq
    #
    @75
    @88
    wph
    @97
    @71
    @83
    @74
    @87
    @70
    @82
    @5
    clt
    breq1
    @97
    @73
    @86
    cc0
    @97
    @72
    @85
    cP
    cpc
    @70
    @82
    @61
    bcxmaslem1
    oveq2d
    eqeq1d
    imbi12d
    imbi2d
    @70
    @89
    wceq
    #
    @75
    @95
    wph
    @98
    @71
    @90
    @74
    @94
    @70
    @89
    @5
    clt
    breq1
    @98
    @73
    @93
    cc0
    @98
    @72
    @92
    cP
    cpc
    @70
    @89
    @61
    bcxmaslem1
    oveq2d
    eqeq1d
    imbi12d
    imbi2d
    @70
    @29
    wceq
    #
    @75
    @68
    wph
    @99
    @71
    @65
    @74
    @66
    @70
    @29
    @5
    clt
    breq1
    @99
    @73
    @64
    cc0
    @99
    @72
    @63
    cP
    cpc
    @70
    @29
    @61
    bcxmaslem1
    oveq2d
    eqeq1d
    imbi12d
    imbi2d
    wph
    @80
    @76
    wph
    @79
    cP
    c1
    cpc
    co
    #
    cc0
    wph
    @78
    c1
    cP
    cpc
    wph
    @77
    cn0
    wcel
    #
    @78
    c1
    wceq
    wph
    @61
    cn0
    wcel
    #
    cc0
    cn0
    wcel
    @101
    wph
    @16
    @102
    @24
    wph
    @10
    @26
    @16
    @102
    wb
    @13
    @27
    @5
    @2
    znn0sub
    syl2anc
    mpbid
    #
    0nn0
    @61
    cc0
    nn0addcl
    sylancl
    @77
    bcn0
    syl
    oveq2d
    wph
    @11
    @100
    cc0
    wceq
    sylow1.p
    cP
    pc1
    syl
    eqtrd
    a1d
    @82
    cn0
    wcel
    #
    wph
    @88
    @95
    wph
    @104
    @88
    @95
    wi
    wph
    @104
    wa
    #
    @88
    @90
    @87
    wi
    @95
    @105
    @90
    @83
    @87
    wph
    @104
    @90
    @83
    wph
    @104
    @90
    wa
    #
    wa
    #
    @82
    @89
    @5
    @104
    @82
    cr
    wcel
    #
    wph
    @90
    @82
    nn0re
    ad2antrl
    #
    @107
    @89
    @104
    @89
    cn
    wcel
    #
    wph
    @90
    @82
    nn0p1nn
    ad2antrl
    #
    nnred
    #
    @107
    @5
    wph
    @69
    @106
    @12
    adantr
    nnred
    #
    @107
    @82
    @109
    ltp1d
    wph
    @104
    @90
    simprr
    #
    lttrd
    expr
    imim1d
    @105
    @90
    @87
    @94
    wph
    @104
    @90
    @87
    @94
    wi
    @87
    @94
    @107
    @86
    cP
    @84
    c1
    caddc
    co
    #
    @89
    cdiv
    co
    #
    cpc
    co
    #
    caddc
    co
    #
    cc0
    @117
    caddc
    co
    #
    wceq
    @86
    cc0
    @117
    caddc
    oveq1
    @107
    @93
    @118
    cc0
    @119
    @107
    @93
    cP
    @85
    @116
    cmul
    co
    #
    cpc
    co
    #
    @118
    @107
    @92
    @120
    cP
    cpc
    @107
    @115
    @89
    cbc
    co
    #
    @92
    @120
    @107
    @115
    @91
    @89
    cbc
    @107
    @61
    @82
    c1
    @107
    @61
    wph
    @102
    @106
    @103
    adantr
    #
    nn0cnd
    #
    @104
    @82
    cc
    wcel
    wph
    @90
    @82
    nn0cn
    ad2antrl
    @107
    1cnd
    addassd
    #
    oveq1d
    @107
    @82
    cc0
    @84
    cfz
    co
    wcel
    #
    @122
    @120
    wceq
    @107
    @126
    @82
    @84
    cle
    wbr
    #
    @107
    @108
    @102
    @127
    @109
    @123
    @82
    @61
    nn0addge2
    syl2anc
    @107
    @82
    @25
    wcel
    @84
    cz
    wcel
    @126
    @127
    wb
    @107
    @82
    cn0
    @25
    wph
    @104
    @90
    simprl
    #
    nn0uz
    syl6eleq
    @107
    @84
    @107
    @61
    @82
    @123
    @128
    nn0addcld
    #
    nn0zd
    #
    @82
    cc0
    @84
    elfz5
    syl2anc
    mpbird
    #
    @82
    @84
    bcp1nk
    syl
    eqtr3d
    oveq2d
    @107
    @11
    @85
    cq
    wcel
    #
    @85
    cc0
    wne
    @116
    cq
    wcel
    #
    @116
    cc0
    wne
    @121
    @118
    wceq
    wph
    @11
    @106
    sylow1.p
    adantr
    #
    @107
    @85
    cn
    wcel
    #
    @132
    @107
    @126
    @135
    @131
    @82
    @84
    bccl2
    syl
    #
    @85
    nnq
    syl
    @107
    @85
    @136
    nnne0d
    @107
    @115
    cz
    wcel
    #
    @110
    @133
    @107
    @84
    @130
    peano2zd
    #
    @111
    @115
    @89
    znq
    syl2anc
    @107
    @116
    @107
    @115
    cn
    wcel
    #
    @110
    @116
    crp
    wcel
    #
    @107
    @84
    cn0
    wcel
    @139
    @129
    @84
    nn0p1nn
    syl
    #
    @111
    @139
    @115
    crp
    wcel
    @89
    crp
    wcel
    @140
    @110
    @115
    nnrp
    @89
    nnrp
    @115
    @89
    rpdivcl
    syl2an
    syl2anc
    rpne0d
    @85
    @116
    cP
    pcqmul
    syl122anc
    eqtrd
    @107
    @119
    cc0
    cc0
    caddc
    co
    cc0
    @107
    @117
    cc0
    cc0
    caddc
    @107
    @117
    cP
    @115
    cpc
    co
    #
    cP
    @89
    cpc
    co
    #
    cmin
    co
    #
    cc0
    @107
    @11
    @137
    @115
    cc0
    wne
    @110
    @117
    @144
    wceq
    @134
    @138
    @107
    @115
    @141
    nnne0d
    @111
    @115
    @89
    cP
    pcdiv
    syl121anc
    @107
    @142
    @143
    @107
    @142
    @143
    cc
    @107
    @142
    cP
    @89
    @61
    caddc
    co
    #
    cpc
    co
    #
    @143
    @107
    @115
    @145
    cP
    cpc
    @107
    @115
    @91
    @145
    @125
    @107
    @61
    @89
    @124
    @107
    @89
    @111
    nncnd
    #
    addcomd
    eqtrd
    oveq2d
    @107
    @143
    @146
    wceq
    @61
    cc0
    @107
    @61
    cc0
    wceq
    #
    wa
    #
    @89
    @145
    cP
    cpc
    @149
    @145
    @89
    cc0
    caddc
    co
    #
    @89
    @149
    @61
    cc0
    @89
    caddc
    @107
    @148
    simpr
    oveq2d
    @107
    @150
    @89
    wceq
    @148
    @107
    @89
    @147
    addid1d
    adantr
    eqtr2d
    oveq2d
    @107
    @61
    cc0
    wne
    #
    wa
    #
    @89
    @61
    cP
    wph
    @11
    @106
    @151
    sylow1.p
    ad2antrr
    #
    @107
    @89
    cq
    wcel
    #
    @151
    @107
    @110
    @154
    @111
    @89
    nnq
    syl
    adantr
    @107
    @61
    cq
    wcel
    #
    @151
    @107
    @61
    cz
    wcel
    #
    @155
    @107
    @61
    @123
    nn0zd
    @61
    zq
    syl
    adantr
    @152
    @143
    cN
    cP
    @61
    cpc
    co
    #
    @107
    @143
    cr
    wcel
    @151
    @107
    @143
    @107
    cP
    @89
    @134
    @111
    pccld
    #
    nn0red
    #
    adantr
    @107
    cN
    cr
    wcel
    @151
    @107
    cN
    wph
    cN
    cn0
    wcel
    #
    @106
    sylow1.n
    adantr
    #
    nn0red
    #
    adantr
    @152
    @157
    @152
    cP
    @61
    @153
    @152
    @61
    cn
    wcel
    #
    @148
    @152
    @61
    cc0
    @107
    @151
    simpr
    neneqd
    @152
    @163
    @148
    @152
    @102
    @163
    @148
    wo
    wph
    @102
    @106
    @151
    @103
    ad2antrr
    #
    @61
    elnn0
    sylib
    ord
    mt3d
    pccld
    nn0red
    @107
    @143
    cN
    clt
    wbr
    #
    @151
    @107
    @90
    @165
    @114
    @107
    cN
    @143
    cle
    wbr
    #
    @5
    @89
    cle
    wbr
    #
    @165
    wn
    @90
    wn
    @107
    @166
    @5
    @89
    cdvds
    wbr
    #
    @167
    @107
    @11
    @89
    cz
    wcel
    @160
    @166
    @168
    wb
    @134
    @107
    @89
    @111
    nnzd
    @161
    cN
    cP
    @89
    pcdvdsb
    syl3anc
    @107
    @10
    @110
    @168
    @167
    wi
    wph
    @10
    @106
    @13
    adantr
    @111
    @5
    @89
    dvdsle
    syl2anc
    sylbid
    @107
    cN
    @143
    @162
    @159
    lenltd
    @107
    @5
    @89
    @113
    @112
    lenltd
    3imtr3d
    mt4d
    adantr
    @152
    cN
    @157
    cle
    wbr
    #
    @5
    @61
    cdvds
    wbr
    #
    wph
    @170
    @106
    @151
    wph
    @17
    @170
    sylow1.d
    wph
    @10
    @26
    @17
    @170
    wb
    @13
    @27
    @5
    @2
    dvdssubr
    syl2anc
    mpbid
    ad2antrr
    @152
    @11
    @156
    @160
    @169
    @170
    wb
    @153
    @152
    @61
    @164
    nn0zd
    wph
    @160
    @106
    @151
    sylow1.n
    ad2antrr
    cN
    cP
    @61
    pcdvdsb
    syl3anc
    mpbird
    ltletrd
    pcadd2
    pm2.61dane
    eqtr4d
    #
    @107
    @143
    @158
    nn0cnd
    eqeltrd
    @171
    subeq0bd
    eqtrd
    oveq2d
    00id
    syl6req
    eqeq12d
    syl5ibr
    expr
    a2d
    syld
    expcom
    a2d
    nn0ind
    mpcom
    mpd
    eqtr3d
    wph
    @55
    @3
    cP
    @5
    cpc
    co
    #
    cmin
    co
    #
    @4
    wph
    @11
    @26
    @2
    cc0
    wne
    @69
    @55
    @173
    wceq
    sylow1.p
    @27
    @60
    @12
    @2
    @5
    cP
    pcdiv
    syl121anc
    wph
    @172
    cN
    @3
    cmin
    wph
    @11
    cN
    cz
    wcel
    @172
    cN
    wceq
    sylow1.p
    wph
    cN
    sylow1.n
    nn0zd
    #
    cN
    cP
    pcid
    syl2anc
    oveq2d
    eqtrd
    oveq12d
    wph
    @4
    wph
    @4
    wph
    @3
    cN
    wph
    @3
    wph
    cP
    @2
    sylow1.p
    @23
    pccld
    nn0zd
    @174
    zsubcld
    zcnd
    addid2d
    3eqtrd
    3eqtr3d
    jca
end

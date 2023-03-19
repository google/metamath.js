include "cslw.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "c1.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cress.mm"
include "cbs.mm"
include "wral.mm"
include "crab.mm"
include "cpr.mm"
include "wss.mm"
include "wrex.mm"
include "wa.mm"
include "copab.mm"
include "eqid.mm"
include "sylow3lem5.mm"
include "wcel.mm"
include "cpgp.mm"
include "slwpgp.mm"
include "syl.mm"
include "cfn.mm"
include "csubg.mm"
include "slwsubg.mm"
include "subgbas.mm"
include "subgss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "cpw.mm"
include "pwfi.mm"
include "sylib.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"
include "sylancl.mm"
include "sylow2a.mm"
include "csn.mm"
include "cmpt.mm"
include "crn.mm"
include "eqcom.mm"
include "adantr.mm"
include "sselda.mm"
include "biantrurd.mm"
include "syl5bb.mm"
include "simpr.mm"
include "simplr.mm"
include "weq.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "vex.mm"
include "mptex.mm"
include "rnex.mm"
include "ovmpt2a.mm"
include "eqeq1d.mm"
include "wb.mm"
include "ad2antlr.mm"
include "conjnmzb.mm"
include "3bitr4d.mm"
include "ralbidva.mm"
include "dfss3.mm"
include "syl6bbr.mm"
include "raleqdv.mm"
include "csg.mm"
include "cgrp.mm"
include "ad2antrr.mm"
include "nmzsubg.mm"
include "subgslw.mm"
include "syl3anc.mm"
include "ssnmz.mm"
include "cvv.mm"
include "cplusg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex2.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "sylow2.mm"
include "cnsg.mm"
include "nmznsg.mm"
include "conjnsg.mm"
include "sylan.mm"
include "eqeq2.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "eqeltrd.mm"
include "eqsstr3d.mm"
include "impbida.mm"
include "3bitr3d.mm"
include "rabbidva.mm"
include "rabsn.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "hashsng.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "cn.mm"
include "cz.mm"
include "cprime.mm"
include "prmnn.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "1zzd.mm"
include "moddvds.mm"
include "mpbird.mm"
include "c2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "clt.mm"
include "eluz2b2.mm"
include "cr.mm"
include "nnre.mm"
include "1mod.mm"
include "sylbi.mm"
include "3syl.mm"

theorem sylow3lem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vg: setvar g
  let vh: setvar h
  let cH: class H
  let vk: setvar k
  assume sylow3.x: |- X = ( Base ` G )
  assume sylow3.g: |- ( ph -> G e. Grp )
  assume sylow3.xf: |- ( ph -> X e. Fin )
  assume sylow3.p: |- ( ph -> P e. Prime )
  assume sylow3lem5.a: |- .+ = ( +g ` G )
  assume sylow3lem5.d: |- .- = ( -g ` G )
  assume sylow3lem5.k: |- ( ph -> K e. ( P pSyl G ) )
  assume sylow3lem5.m: |- .(+) = ( x e. K , y e. ( P pSyl G ) |-> ran ( z e. y |-> ( ( x .+ z ) .- x ) ) )
  assume sylow3lem6.n: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. s <-> ( y .+ x ) e. s ) }

  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint .(+) s
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint N z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G s
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint P s
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint .- a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .- b
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .- c
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .- v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .- w
  disjoint a g
  disjoint a h
  disjoint a s
  disjoint .(+) a
  disjoint b g
  disjoint b h
  disjoint b s
  disjoint .(+) b
  disjoint c g
  disjoint c h
  disjoint c s
  disjoint .(+) c
  disjoint g h
  disjoint g s
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .(+) g
  disjoint h s
  disjoint h u
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint .(+) h
  disjoint s u
  disjoint s w
  disjoint .(+) u
  disjoint .(+) w
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint g v
  disjoint K g
  disjoint h v
  disjoint K h
  disjoint s v
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint g k
  disjoint N g
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint N k
  disjoint N u
  disjoint N w
  disjoint a k
  disjoint X a
  disjoint b k
  disjoint X b
  disjoint c k
  disjoint X c
  disjoint X g
  disjoint h k
  disjoint X h
  disjoint k x
  disjoint k y
  disjoint X k
  disjoint X u
  disjoint X w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint k s
  disjoint G k
  disjoint G u
  disjoint G w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph u
  disjoint ph w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ g
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P u
  disjoint P w
  assert |- ( ph -> ( ( # ` ( P pSyl G ) ) mod P ) = 1 )

  proof
    wph
    cP
    cG
    cslw
    co
    #
    chash
    cfv
    #
    cP
    cmo
    co
    #
    c1
    cP
    cmo
    co
    #
    c1
    wph
    @2
    @3
    wceq
    #
    cP
    @1
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    wph
    cP
    @1
    vg
    cv
    #
    vs
    cv
    #
    c.po
    co
    #
    @8
    wceq
    #
    vg
    cG
    cK
    cress
    co
    #
    cbs
    cfv
    #
    wral
    #
    vs
    @0
    crab
    #
    chash
    cfv
    #
    cmin
    co
    @5
    cdvds
    wph
    vz
    vw
    vs
    cP
    c.po
    vz
    cv
    #
    vw
    cv
    #
    cpr
    @0
    wss
    vh
    cv
    @16
    c.po
    co
    @17
    wceq
    vh
    @12
    wrex
    wa
    vz
    vw
    copab
    #
    vh
    vg
    @11
    @12
    @0
    @14
    @12
    eqid
    wph
    vx
    vy
    vz
    cP
    c.pl
    c.po
    cG
    cK
    c.mi
    cX
    sylow3.x
    sylow3.g
    sylow3.xf
    sylow3.p
    sylow3lem5.a
    sylow3lem5.d
    sylow3lem5.k
    sylow3lem5.m
    sylow3lem5
    wph
    cK
    @0
    wcel
    #
    cP
    @11
    cpgp
    wbr
    sylow3lem5.k
    cP
    @11
    cG
    cK
    @11
    eqid
    #
    slwpgp
    syl
    wph
    cK
    @12
    cfn
    wph
    cK
    cG
    csubg
    cfv
    #
    wcel
    #
    cK
    @12
    wceq
    #
    wph
    @19
    @22
    sylow3lem5.k
    cP
    cG
    cK
    slwsubg
    syl
    #
    cK
    cG
    @11
    @20
    subgbas
    syl
    #
    wph
    cX
    cfn
    wcel
    #
    cK
    cX
    wss
    #
    cK
    cfn
    wcel
    sylow3.xf
    wph
    @22
    @27
    @24
    cX
    cK
    cG
    sylow3.x
    subgss
    syl
    #
    cX
    cK
    ssfi
    syl2anc
    eqeltrrd
    wph
    cX
    cpw
    #
    cfn
    wcel
    #
    @0
    @29
    wss
    @0
    cfn
    wcel
    #
    wph
    @26
    @30
    sylow3.xf
    cX
    pwfi
    sylib
    vx
    @0
    @29
    vx
    cv
    #
    @0
    wcel
    #
    @32
    cX
    wss
    #
    @32
    @29
    wcel
    @33
    @32
    @21
    wcel
    @34
    cP
    cG
    @32
    slwsubg
    cX
    @32
    cG
    sylow3.x
    subgss
    syl
    vx
    cX
    selpw
    sylibr
    ssriv
    @29
    @0
    ssfi
    sylancl
    #
    @14
    eqid
    @18
    eqid
    sylow2a
    wph
    @15
    c1
    @1
    cmin
    wph
    @15
    cK
    csn
    #
    chash
    cfv
    #
    c1
    wph
    @14
    @36
    chash
    wph
    @14
    @8
    cK
    wceq
    #
    vs
    @0
    crab
    #
    @36
    wph
    @13
    @38
    vs
    @0
    wph
    @8
    @0
    wcel
    #
    wa
    #
    @10
    vg
    cK
    wral
    #
    cK
    cN
    wss
    #
    @13
    @38
    @41
    @42
    @7
    cN
    wcel
    #
    vg
    cK
    wral
    @43
    @41
    @10
    @44
    vg
    cK
    @41
    @7
    cK
    wcel
    #
    wa
    #
    vz
    @8
    @7
    @16
    c.pl
    co
    #
    @7
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    @8
    wceq
    #
    @7
    cX
    wcel
    #
    @8
    @50
    wceq
    #
    wa
    #
    @10
    @44
    @51
    @53
    @46
    @54
    @50
    @8
    eqcom
    @46
    @52
    @53
    @41
    cK
    cX
    @7
    wph
    @27
    @40
    @28
    adantr
    sselda
    biantrurd
    syl5bb
    @46
    @9
    @50
    @8
    @46
    @45
    @40
    @9
    @50
    wceq
    @41
    @45
    simpr
    wph
    @40
    @45
    simplr
    vx
    vy
    @7
    @8
    cK
    @0
    vz
    vy
    cv
    #
    @32
    @16
    c.pl
    co
    #
    @32
    c.mi
    co
    #
    cmpt
    #
    crn
    @50
    c.po
    vx
    vg
    weq
    #
    vy
    vs
    weq
    #
    wa
    #
    @58
    @49
    @61
    vz
    @55
    @57
    @8
    @48
    @59
    @60
    simpr
    @61
    @56
    @47
    @32
    @7
    c.mi
    @61
    @32
    @7
    @16
    c.pl
    @59
    @60
    simpl
    #
    oveq1d
    @62
    oveq12d
    mpteq12dv
    rneqd
    sylow3lem5.m
    @49
    vz
    @8
    @48
    vs
    vex
    mptex
    rnex
    ovmpt2a
    syl2anc
    eqeq1d
    @46
    @8
    @21
    wcel
    #
    @44
    @54
    wb
    @40
    @63
    wph
    @45
    cP
    cG
    @8
    slwsubg
    #
    ad2antlr
    vz
    vx
    vy
    @7
    c.pl
    @8
    @49
    cG
    c.mi
    cN
    cX
    sylow3.x
    sylow3lem5.a
    sylow3lem5.d
    @49
    eqid
    sylow3lem6.n
    conjnmzb
    syl
    3bitr4d
    ralbidva
    vg
    cK
    cN
    dfss3
    syl6bbr
    @41
    @10
    vg
    cK
    @12
    wph
    @23
    @40
    @25
    adantr
    raleqdv
    @41
    @43
    @38
    @41
    @43
    wa
    #
    cK
    vz
    @8
    @47
    @7
    cG
    cN
    cress
    co
    #
    csg
    cfv
    #
    co
    cmpt
    #
    crn
    #
    wceq
    #
    vg
    @66
    cbs
    cfv
    #
    wrex
    @38
    @65
    vz
    cP
    c.pl
    vg
    @66
    cK
    @8
    @67
    @71
    @71
    eqid
    #
    @65
    cN
    @71
    cfn
    @65
    cN
    @21
    wcel
    #
    cN
    @71
    wceq
    @65
    cG
    cgrp
    wcel
    #
    @73
    wph
    @74
    @40
    @43
    sylow3.g
    ad2antrr
    vx
    vy
    c.pl
    @8
    cG
    cN
    cX
    sylow3lem6.n
    sylow3.x
    sylow3lem5.a
    nmzsubg
    syl
    #
    cN
    cG
    @66
    @66
    eqid
    #
    subgbas
    syl
    @65
    @26
    cN
    cX
    wss
    #
    cN
    cfn
    wcel
    wph
    @26
    @40
    @43
    sylow3.xf
    ad2antrr
    @65
    @73
    @77
    @75
    cX
    cN
    cG
    sylow3.x
    subgss
    syl
    cX
    cN
    ssfi
    syl2anc
    eqeltrrd
    @65
    @73
    @19
    @43
    cK
    cP
    @66
    cslw
    co
    #
    wcel
    @75
    wph
    @19
    @40
    @43
    sylow3lem5.k
    ad2antrr
    @41
    @43
    simpr
    cP
    cN
    cG
    @66
    cK
    @76
    subgslw
    syl3anc
    @65
    @73
    @40
    @8
    cN
    wss
    #
    @8
    @78
    wcel
    @75
    wph
    @40
    @43
    simplr
    @65
    @63
    @79
    @40
    @63
    wph
    @43
    @64
    ad2antlr
    #
    vx
    vy
    c.pl
    @8
    cG
    cN
    cX
    sylow3lem6.n
    sylow3.x
    sylow3lem5.a
    ssnmz
    #
    syl
    cP
    cN
    cG
    @66
    @8
    @76
    subgslw
    syl3anc
    cN
    cvv
    wcel
    c.pl
    @66
    cplusg
    cfv
    wceq
    @32
    @55
    c.pl
    co
    @8
    wcel
    @55
    @32
    c.pl
    co
    @8
    wcel
    wb
    vy
    cX
    wral
    vx
    cX
    cN
    sylow3lem6.n
    cX
    cG
    cbs
    cfv
    cvv
    sylow3.x
    cG
    cbs
    fvex
    eqeltri
    rabex2
    cN
    c.pl
    cG
    @66
    cvv
    @76
    sylow3lem5.a
    ressplusg
    ax-mp
    #
    @67
    eqid
    #
    sylow2
    @65
    @70
    @38
    vg
    @71
    @65
    @7
    @71
    wcel
    #
    wa
    @38
    @70
    @8
    @69
    wceq
    #
    @65
    @8
    @66
    cnsg
    cfv
    wcel
    #
    @84
    @85
    @65
    @63
    @86
    @80
    vx
    vy
    c.pl
    @8
    cG
    @66
    cN
    cX
    sylow3lem6.n
    sylow3.x
    sylow3lem5.a
    @76
    nmznsg
    syl
    vz
    @7
    c.pl
    @8
    @68
    @66
    @67
    @71
    @72
    @82
    @83
    @68
    eqid
    conjnsg
    sylan
    cK
    @69
    @8
    eqeq2
    syl5ibrcom
    rexlimdva
    mpd
    @41
    @38
    wa
    #
    cK
    @8
    cN
    @41
    @38
    simpr
    #
    @87
    @63
    @79
    @87
    @8
    cK
    @21
    @88
    wph
    @22
    @40
    @38
    @24
    ad2antrr
    eqeltrd
    @81
    syl
    eqsstr3d
    impbida
    3bitr3d
    rabbidva
    wph
    @19
    @39
    @36
    wceq
    sylow3lem5.k
    vs
    @0
    cK
    rabsn
    syl
    eqtrd
    fveq2d
    wph
    @19
    @37
    c1
    wceq
    sylow3lem5.k
    cK
    @0
    hashsng
    syl
    eqtrd
    oveq2d
    breqtrd
    wph
    cP
    cn
    wcel
    #
    @1
    cz
    wcel
    c1
    cz
    wcel
    @4
    @6
    wb
    wph
    cP
    cprime
    wcel
    #
    @89
    sylow3.p
    cP
    prmnn
    syl
    wph
    @1
    wph
    @31
    @1
    cn0
    wcel
    @35
    @0
    hashcl
    syl
    nn0zd
    wph
    1zzd
    @1
    c1
    cP
    moddvds
    syl3anc
    mpbird
    wph
    @90
    cP
    c2
    cuz
    cfv
    wcel
    #
    @3
    c1
    wceq
    #
    sylow3.p
    cP
    prmuz2
    @91
    @89
    c1
    cP
    clt
    wbr
    #
    wa
    @92
    cP
    eluz2b2
    @89
    cP
    cr
    wcel
    @93
    @92
    cP
    nnre
    cP
    1mod
    sylan
    sylbi
    3syl
    eqtrd
end

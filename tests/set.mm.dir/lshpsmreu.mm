include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wreu.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "cfv.mm"
include "wcel.mm"
include "eleqtrrd.mm"
include "csubg.mm"
include "wb.mm"
include "clss.mm"
include "clmod.mm"
include "wss.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "lshplss.mm"
include "sseldd.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "lsmelval.mm"
include "mpbid.mm"
include "wex.mm"
include "df-rex.mm"
include "lspsnel.mm"
include "anbi1d.mm"
include "r19.41v.mm"
include "syl6bbr.mm"
include "exbidv.mm"
include "rexcom4.mm"
include "ovex.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "rexcom.mm"
include "sylib.mm"
include "oveq1.mm"
include "cbvrexv.mm"
include "w3a.mm"
include "c0g.mm"
include "ccntz.mm"
include "simp11l.mm"
include "cin.mm"
include "lshpdisj.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "simp12.mm"
include "simp2.mm"
include "simp1rl.mm"
include "3ad2ant1.mm"
include "lspsneli.mm"
include "simp1rr.mm"
include "simp13.mm"
include "simp3.mm"
include "eqtr3d.mm"
include "subgdisj2.mm"
include "lshpne0.mm"
include "lvecvscan2.mm"
include "rexlimdv3a.mm"
include "syl5bi.mm"
include "impd.mm"
include "ralrimivva.mm"
include "oveq2d.mm"
include "reu4.mm"
include "sylanbrc.mm"
include "cbvreuv.mm"
include "reubii.mm"
include "bitri.mm"

theorem lshpsmreu
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  let vz: setvar z
  assume lshpsmreu.v: |- V = ( Base ` W )
  assume lshpsmreu.a: |- .+ = ( +g ` W )
  assume lshpsmreu.n: |- N = ( LSpan ` W )
  assume lshpsmreu.p: |- .(+) = ( LSSum ` W )
  assume lshpsmreu.h: |- H = ( LSHyp ` W )
  assume lshpsmreu.w: |- ( ph -> W e. LVec )
  assume lshpsmreu.u: |- ( ph -> U e. H )
  assume lshpsmreu.z: |- ( ph -> Z e. V )
  assume lshpsmreu.x: |- ( ph -> X e. V )
  assume lshpsmreu.e: |- ( ph -> ( U .(+) ( N ` { Z } ) ) = V )
  assume lshpsmreu.d: |- D = ( Scalar ` W )
  assume lshpsmreu.k: |- K = ( Base ` D )
  assume lshpsmreu.t: |- .x. = ( .s ` W )

  disjoint k y
  disjoint .+ k
  disjoint .+ y
  disjoint K k
  disjoint .x. k
  disjoint .x. y
  disjoint U k
  disjoint U y
  disjoint X k
  disjoint X y
  disjoint Z k
  disjoint Z y
  disjoint a b
  disjoint a c
  disjoint a k
  disjoint a l
  disjoint a y
  disjoint a z
  disjoint .+ a
  disjoint b c
  disjoint b k
  disjoint b l
  disjoint b y
  disjoint b z
  disjoint .+ b
  disjoint c k
  disjoint c l
  disjoint c y
  disjoint c z
  disjoint .+ c
  disjoint k l
  disjoint k z
  disjoint l y
  disjoint l z
  disjoint .+ l
  disjoint y z
  disjoint .+ z
  disjoint D b
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K l
  disjoint K z
  disjoint N b
  disjoint N c
  disjoint N z
  disjoint .x. a
  disjoint .x. b
  disjoint .x. c
  disjoint .x. l
  disjoint .x. z
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U l
  disjoint U z
  disjoint V b
  disjoint W b
  disjoint W c
  disjoint W z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X l
  disjoint X z
  disjoint Z a
  disjoint Z b
  disjoint Z c
  disjoint Z l
  disjoint Z z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint l ph
  disjoint ph z
  assert |- ( ph -> E! k e. K E. y e. U X = ( y .+ ( k .x. Z ) ) )

  proof
    wph
    cX
    vc
    cv
    #
    vb
    cv
    #
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vc
    cU
    wrex
    #
    vb
    cK
    wreu
    #
    cX
    vy
    cv
    #
    vk
    cv
    #
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    #
    vk
    cK
    wreu
    #
    wph
    @5
    vb
    cK
    wrex
    #
    @5
    cX
    @0
    vl
    cv
    #
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vc
    cU
    wrex
    #
    wa
    vb
    vl
    weq
    #
    wi
    #
    vl
    cK
    wral
    vb
    cK
    wral
    @6
    wph
    @4
    vb
    cK
    wrex
    #
    vc
    cU
    wrex
    #
    @14
    wph
    cX
    @0
    vz
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vz
    cZ
    csn
    cN
    cfv
    #
    wrex
    #
    vc
    cU
    wrex
    #
    @23
    wph
    cX
    cU
    @27
    c.po
    co
    #
    wcel
    #
    @29
    wph
    cX
    cV
    @30
    lshpsmreu.x
    lshpsmreu.e
    eleqtrrd
    wph
    cU
    cW
    csubg
    cfv
    #
    wcel
    #
    @27
    @32
    wcel
    #
    @31
    @29
    wb
    wph
    cW
    clss
    cfv
    #
    @32
    cU
    wph
    cW
    clmod
    wcel
    #
    @35
    @32
    wss
    wph
    cW
    clvec
    wcel
    #
    @36
    lshpsmreu.w
    cW
    lveclmod
    #
    syl
    #
    @35
    cW
    @35
    eqid
    #
    lsssssubg
    syl
    #
    wph
    @35
    cU
    cH
    cW
    @40
    lshpsmreu.h
    @39
    lshpsmreu.u
    lshplss
    sseldd
    #
    wph
    @35
    @32
    @27
    @41
    wph
    @36
    cZ
    cV
    wcel
    #
    @27
    @35
    wcel
    @39
    lshpsmreu.z
    @35
    cN
    cV
    cW
    cZ
    lshpsmreu.v
    @40
    lshpsmreu.n
    lspsncl
    syl2anc
    sseldd
    #
    vc
    vz
    c.pl
    c.po
    cU
    @27
    cW
    cX
    lshpsmreu.a
    lshpsmreu.p
    lsmelval
    syl2anc
    mpbid
    wph
    @28
    @22
    vc
    cU
    @28
    @24
    @27
    wcel
    #
    @26
    wa
    #
    vz
    wex
    #
    wph
    @22
    @26
    vz
    @27
    df-rex
    wph
    @47
    @24
    @2
    wceq
    #
    @26
    wa
    #
    vb
    cK
    wrex
    #
    vz
    wex
    #
    @22
    wph
    @46
    @50
    vz
    wph
    @46
    @48
    vb
    cK
    wrex
    #
    @26
    wa
    @50
    wph
    @45
    @52
    @26
    wph
    @36
    @43
    @45
    @52
    wb
    @39
    lshpsmreu.z
    c.x
    @24
    vb
    cD
    cK
    cN
    cV
    cW
    cZ
    lshpsmreu.d
    lshpsmreu.k
    lshpsmreu.v
    lshpsmreu.t
    lshpsmreu.n
    lspsnel
    syl2anc
    anbi1d
    @48
    @26
    vb
    cK
    r19.41v
    syl6bbr
    exbidv
    @51
    @49
    vz
    wex
    #
    vb
    cK
    wrex
    @22
    @49
    vb
    vz
    cK
    rexcom4
    @53
    @4
    vb
    cK
    @26
    @4
    vz
    @2
    @1
    cZ
    c.x
    ovex
    @48
    @25
    @3
    cX
    @24
    @2
    @0
    c.pl
    oveq2
    eqeq2d
    ceqsexv
    rexbii
    bitr3i
    syl6bb
    syl5bb
    rexbidv
    mpbid
    @4
    vc
    vb
    cU
    cK
    rexcom
    sylib
    wph
    @21
    vb
    vl
    cK
    cK
    wph
    @1
    cK
    wcel
    #
    @15
    cK
    wcel
    #
    wa
    #
    wa
    #
    @5
    @19
    @20
    @5
    cX
    va
    cv
    #
    @2
    c.pl
    co
    #
    wceq
    #
    va
    cU
    wrex
    @57
    @19
    @20
    wi
    #
    @4
    @60
    vc
    va
    cU
    vc
    va
    weq
    @3
    @59
    cX
    @0
    @58
    @2
    c.pl
    oveq1
    eqeq2d
    cbvrexv
    @57
    @60
    @61
    va
    cU
    @57
    @58
    cU
    wcel
    #
    @60
    w3a
    #
    @18
    @20
    vc
    cU
    @63
    @0
    cU
    wcel
    #
    @18
    w3a
    #
    @2
    @16
    wceq
    @20
    @65
    @58
    @2
    @0
    @16
    c.pl
    cU
    @27
    cW
    cW
    c0g
    cfv
    #
    cW
    ccntz
    cfv
    #
    lshpsmreu.a
    @66
    eqid
    #
    @67
    eqid
    #
    @65
    wph
    @33
    wph
    @56
    @62
    @60
    @64
    @18
    simp11l
    #
    @42
    syl
    #
    @65
    wph
    @34
    @70
    @44
    syl
    #
    @65
    wph
    cU
    @27
    cin
    @66
    csn
    wceq
    @70
    wph
    c.po
    cU
    cH
    cN
    cV
    cW
    cZ
    @66
    lshpsmreu.v
    @68
    lshpsmreu.n
    lshpsmreu.p
    lshpsmreu.h
    lshpsmreu.w
    lshpsmreu.u
    lshpsmreu.z
    lshpsmreu.e
    lshpdisj
    syl
    @65
    cU
    @27
    cW
    @67
    @69
    @65
    @36
    cW
    cabl
    wcel
    @65
    @37
    @36
    @65
    wph
    @37
    @70
    lshpsmreu.w
    syl
    #
    @38
    syl
    #
    cW
    lmodabl
    syl
    @71
    @72
    ablcntzd
    @57
    @62
    @60
    @64
    @18
    simp12
    @63
    @64
    @18
    simp2
    @65
    @1
    c.x
    cD
    cK
    cN
    cV
    cW
    cZ
    lshpsmreu.v
    lshpsmreu.t
    lshpsmreu.d
    lshpsmreu.k
    lshpsmreu.n
    @74
    @63
    @64
    @54
    @18
    @54
    @55
    wph
    @62
    @60
    simp1rl
    3ad2ant1
    #
    @65
    wph
    @43
    @70
    lshpsmreu.z
    syl
    #
    lspsneli
    @65
    @15
    c.x
    cD
    cK
    cN
    cV
    cW
    cZ
    lshpsmreu.v
    lshpsmreu.t
    lshpsmreu.d
    lshpsmreu.k
    lshpsmreu.n
    @74
    @63
    @64
    @55
    @18
    @54
    @55
    wph
    @62
    @60
    simp1rr
    3ad2ant1
    #
    @76
    lspsneli
    @65
    cX
    @59
    @17
    @57
    @62
    @60
    @64
    @18
    simp13
    @63
    @64
    @18
    simp3
    eqtr3d
    subgdisj2
    @65
    @1
    @15
    c.x
    cD
    cK
    cV
    cW
    cZ
    @66
    lshpsmreu.v
    lshpsmreu.t
    lshpsmreu.d
    lshpsmreu.k
    @68
    @73
    @75
    @77
    @76
    @65
    c.po
    cU
    cH
    cN
    cV
    cW
    cZ
    @66
    lshpsmreu.v
    lshpsmreu.n
    lshpsmreu.p
    lshpsmreu.h
    @68
    @74
    @65
    wph
    cU
    cH
    wcel
    @70
    lshpsmreu.u
    syl
    @76
    @65
    wph
    @30
    cV
    wceq
    @70
    lshpsmreu.e
    syl
    lshpne0
    lvecvscan2
    mpbid
    rexlimdv3a
    rexlimdv3a
    syl5bi
    impd
    ralrimivva
    @5
    @19
    vb
    vl
    cK
    @20
    @4
    @18
    vc
    cU
    @20
    @3
    @17
    cX
    @20
    @2
    @16
    @0
    c.pl
    @1
    @15
    cZ
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    reu4
    sylanbrc
    @6
    cX
    @0
    @9
    c.pl
    co
    #
    wceq
    #
    vc
    cU
    wrex
    #
    vk
    cK
    wreu
    @13
    @5
    @80
    vb
    vk
    cK
    vb
    vk
    weq
    #
    @4
    @79
    vc
    cU
    @81
    @3
    @78
    cX
    @81
    @2
    @9
    @0
    c.pl
    @1
    @8
    cZ
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    cbvreuv
    @80
    @12
    vk
    cK
    @79
    @11
    vc
    vy
    cU
    vc
    vy
    weq
    @78
    @10
    cX
    @0
    @7
    @9
    c.pl
    oveq1
    eqeq2d
    cbvrexv
    reubii
    bitri
    sylib
end

include "cv.mm"
include "co.mm"
include "wceq.mm"
include "crab.mm"
include "cin.mm"
include "wss.mm"
include "wcel.mm"
include "wb.mm"
include "wral.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "wa.mm"
include "cmpt.mm"
include "crn.mm"
include "cslw.mm"
include "cvv.mm"
include "simpr.mm"
include "adantr.mm"
include "mptexg.mm"
include "rnexg.mm"
include "3syl.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "csubg.mm"
include "cfv.mm"
include "slwsubg.mm"
include "syl.mm"
include "eqid.mm"
include "conjnmz.mm"
include "sylan.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "simprl.mm"
include "eqtr3d.mm"
include "eleq2d.mm"
include "wrex.mm"
include "ovex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rnmpt.mm"
include "elab2.mm"
include "simprr.mm"
include "cgrp.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "subgss.mm"
include "sseldd.mm"
include "grpaddsubass.mm"
include "syl13anc.mm"
include "eqtr2d.mm"
include "grpsubcl.mm"
include "simplrr.mm"
include "grplcan.mm"
include "mpbid.mm"
include "grpsubadd.mm"
include "eqeltrd.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "oveq2.mm"
include "fvmpt.mm"
include "grpass.mm"
include "grpcl.mm"
include "grppncan.mm"
include "3eqtr2d.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "impbid.mm"
include "bitrd.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "elnmz.mm"
include "sylanbrc.mm"
include "impbida.mm"
include "rabbi2dva.mm"
include "syl5eqr.mm"
include "syl6reqr.mm"

theorem sylow3lem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vv: setvar v
  let vw: setvar w
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vk: setvar k
  assume sylow3.x: |- X = ( Base ` G )
  assume sylow3.g: |- ( ph -> G e. Grp )
  assume sylow3.xf: |- ( ph -> X e. Fin )
  assume sylow3.p: |- ( ph -> P e. Prime )
  assume sylow3lem1.a: |- .+ = ( +g ` G )
  assume sylow3lem1.d: |- .- = ( -g ` G )
  assume sylow3lem1.m: |- .(+) = ( x e. X , y e. ( P pSyl G ) |-> ran ( z e. y |-> ( ( x .+ z ) .- x ) ) )
  assume sylow3lem2.k: |- ( ph -> K e. ( P pSyl G ) )
  assume sylow3lem2.h: |- H = { u e. X | ( u .(+) K ) = K }
  assume sylow3lem2.n: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. K <-> ( y .+ x ) e. K ) }

  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint .(+) u
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint H x
  disjoint H y
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint N u
  disjoint N z
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint P u
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
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint .(+) s
  disjoint .(+) w
  disjoint H g
  disjoint g v
  disjoint K g
  disjoint h v
  disjoint K h
  disjoint s v
  disjoint K s
  disjoint K v
  disjoint K w
  disjoint g k
  disjoint N g
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint N k
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
  disjoint X w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint k s
  disjoint G k
  disjoint G s
  disjoint G w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph s
  disjoint ph w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ g
  disjoint .+ v
  disjoint .+ w
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P s
  disjoint P w
  assert |- ( ph -> H = N )

  proof
    wph
    cN
    vu
    cv
    #
    cK
    c.po
    co
    #
    cK
    wceq
    #
    vu
    cX
    crab
    #
    cH
    wph
    cN
    cX
    cN
    cin
    #
    @3
    cN
    cX
    wss
    @4
    cN
    wceq
    cN
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    cK
    wcel
    @6
    @5
    c.pl
    co
    cK
    wcel
    wb
    vy
    cX
    wral
    #
    vx
    cX
    crab
    cX
    sylow3lem2.n
    @7
    vx
    cX
    ssrab2
    eqsstri
    cN
    cX
    sseqin2
    mpbi
    wph
    @2
    vu
    cX
    cN
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @0
    cN
    wcel
    #
    @2
    @9
    @10
    wa
    @1
    vz
    cK
    @0
    vz
    cv
    #
    c.pl
    co
    #
    @0
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    cK
    @9
    @1
    @15
    wceq
    #
    @10
    @9
    @8
    cK
    cP
    cG
    cslw
    co
    #
    wcel
    #
    @15
    cvv
    wcel
    #
    @16
    wph
    @8
    simpr
    wph
    @18
    @8
    sylow3lem2.k
    adantr
    #
    @9
    @18
    @14
    cvv
    wcel
    @19
    @20
    vz
    cK
    @13
    @17
    mptexg
    @14
    cvv
    rnexg
    3syl
    vx
    vy
    @0
    cK
    cX
    @17
    vz
    @6
    @5
    @11
    c.pl
    co
    #
    @5
    c.mi
    co
    #
    cmpt
    #
    crn
    @15
    c.po
    cvv
    @5
    @0
    wceq
    #
    @6
    cK
    wceq
    #
    wa
    #
    @23
    @14
    @26
    vz
    @6
    @22
    cK
    @13
    @24
    @25
    simpr
    @26
    @21
    @12
    @5
    @0
    c.mi
    @26
    @5
    @0
    @11
    c.pl
    @24
    @25
    simpl
    #
    oveq1d
    @27
    oveq12d
    mpteq12dv
    rneqd
    sylow3lem1.m
    ovmpt2ga
    syl3anc
    #
    adantr
    @9
    cK
    cG
    csubg
    cfv
    wcel
    #
    @10
    cK
    @15
    wceq
    wph
    @29
    @8
    wph
    @18
    @29
    sylow3lem2.k
    cP
    cG
    cK
    slwsubg
    syl
    #
    adantr
    vz
    vx
    vy
    @0
    c.pl
    cK
    @14
    cG
    c.mi
    cN
    cX
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    @14
    eqid
    #
    sylow3lem2.n
    conjnmz
    sylan
    eqtr4d
    @9
    @2
    wa
    #
    @8
    @0
    vw
    cv
    #
    c.pl
    co
    #
    cK
    wcel
    #
    @33
    @0
    c.pl
    co
    #
    cK
    wcel
    #
    wb
    #
    vw
    cX
    wral
    @10
    wph
    @8
    @2
    simplr
    @32
    @38
    vw
    cX
    @9
    @2
    @33
    cX
    wcel
    #
    @38
    @9
    @2
    @39
    wa
    #
    wa
    #
    @35
    @34
    @15
    wcel
    #
    @37
    @41
    cK
    @15
    @34
    @41
    @1
    cK
    @15
    @9
    @2
    @39
    simprl
    @9
    @16
    @40
    @28
    adantr
    eqtr3d
    eleq2d
    @41
    @42
    @37
    @42
    @34
    @13
    wceq
    #
    vz
    cK
    wrex
    #
    @41
    @37
    vv
    cv
    #
    @13
    wceq
    #
    vz
    cK
    wrex
    @44
    vv
    @34
    @15
    @0
    @33
    c.pl
    ovex
    @45
    @34
    wceq
    @46
    @43
    vz
    cK
    @45
    @34
    @13
    eqeq1
    rexbidv
    vz
    vv
    cK
    @13
    @14
    @31
    rnmpt
    elab2
    @41
    @43
    @37
    vz
    cK
    @41
    @11
    cK
    wcel
    #
    @43
    wa
    #
    wa
    #
    @36
    @11
    cK
    @49
    @11
    @0
    c.mi
    co
    #
    @33
    wceq
    #
    @36
    @11
    wceq
    #
    @49
    @0
    @50
    c.pl
    co
    #
    @34
    wceq
    #
    @51
    @49
    @34
    @13
    @53
    @41
    @47
    @43
    simprr
    @49
    cG
    cgrp
    wcel
    #
    @8
    @11
    cX
    wcel
    #
    @8
    @13
    @53
    wceq
    wph
    @55
    @8
    @40
    @48
    sylow3.g
    ad3antrrr
    #
    wph
    @8
    @40
    @48
    simpllr
    #
    @49
    cK
    cX
    @11
    wph
    cK
    cX
    wss
    #
    @8
    @40
    @48
    wph
    @29
    @59
    @30
    cX
    cK
    cG
    sylow3.x
    subgss
    syl
    ad3antrrr
    @41
    @47
    @43
    simprl
    #
    sseldd
    #
    @58
    cX
    c.pl
    cG
    c.mi
    @0
    @11
    @0
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    grpaddsubass
    syl13anc
    eqtr2d
    @49
    @55
    @50
    cX
    wcel
    #
    @39
    @8
    @54
    @51
    wb
    @57
    @49
    @55
    @56
    @8
    @62
    @57
    @61
    @58
    cX
    cG
    c.mi
    @11
    @0
    sylow3.x
    sylow3lem1.d
    grpsubcl
    syl3anc
    @9
    @2
    @39
    @48
    simplrr
    #
    @58
    cX
    c.pl
    cG
    @50
    @33
    @0
    sylow3.x
    sylow3lem1.a
    grplcan
    syl13anc
    mpbid
    @49
    @55
    @56
    @8
    @39
    @51
    @52
    wb
    @57
    @61
    @58
    @63
    cX
    c.pl
    cG
    c.mi
    @11
    @0
    @33
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    grpsubadd
    syl13anc
    mpbid
    @60
    eqeltrd
    rexlimdvaa
    syl5bi
    @41
    @37
    @42
    @41
    @37
    wa
    #
    @36
    @14
    cfv
    #
    @34
    @15
    @64
    @65
    @0
    @36
    c.pl
    co
    #
    @0
    c.mi
    co
    #
    @34
    @0
    c.pl
    co
    #
    @0
    c.mi
    co
    #
    @34
    @64
    @37
    @65
    @67
    wceq
    @41
    @37
    simpr
    #
    vz
    @36
    @13
    @67
    cK
    @14
    @11
    @36
    wceq
    @12
    @66
    @0
    c.mi
    @11
    @36
    @0
    c.pl
    oveq2
    oveq1d
    @31
    @66
    @0
    c.mi
    ovex
    fvmpt
    syl
    @64
    @68
    @66
    @0
    c.mi
    @64
    @55
    @8
    @39
    @8
    @68
    @66
    wceq
    wph
    @55
    @8
    @40
    @37
    sylow3.g
    ad3antrrr
    #
    wph
    @8
    @40
    @37
    simpllr
    #
    @9
    @2
    @39
    @37
    simplrr
    #
    @72
    cX
    c.pl
    cG
    @0
    @33
    @0
    sylow3.x
    sylow3lem1.a
    grpass
    syl13anc
    oveq1d
    @64
    @55
    @34
    cX
    wcel
    #
    @8
    @69
    @34
    wceq
    @71
    @64
    @55
    @8
    @39
    @74
    @71
    @72
    @73
    cX
    c.pl
    cG
    @0
    @33
    sylow3.x
    sylow3lem1.a
    grpcl
    syl3anc
    @72
    cX
    c.pl
    cG
    c.mi
    @34
    @0
    sylow3.x
    sylow3lem1.a
    sylow3lem1.d
    grppncan
    syl3anc
    3eqtr2d
    @64
    @14
    cK
    wfn
    @37
    @65
    @15
    wcel
    vz
    cK
    @13
    @14
    @12
    @0
    c.mi
    ovex
    @31
    fnmpti
    @70
    cK
    @36
    @14
    fnfvelrn
    sylancr
    eqeltrrd
    ex
    impbid
    bitrd
    anassrs
    ralrimiva
    vx
    vy
    vw
    @0
    c.pl
    cK
    cN
    cX
    sylow3lem2.n
    elnmz
    sylanbrc
    impbida
    rabbi2dva
    syl5eqr
    sylow3lem2.h
    syl6reqr
end

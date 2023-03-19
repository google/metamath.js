include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cbs.mm"
include "wss.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "wn.mm"
include "cvsca.mm"
include "csn.mm"
include "cdif.mm"
include "wo.mm"
include "wral.mm"
include "wi.mm"
include "ax-1.mm"
include "2a1d.mm"
include "cminusg.mm"
include "wne.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "adantl.mm"
include "com12.mm"
include "syl.mm"
include "adantr.mm"
include "impcom.mm"
include "biantrurd.mm"
include "df-ne.mm"
include "bicomi.mm"
include "eldifsn.mm"
include "3bitr4g.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "eqid.mm"
include "grpinvnzcl.mm"
include "sylan.mm"
include "ex.mm"
include "sylbid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "notbid.mm"
include "orbi2d.mm"
include "ralbidv.mm"
include "rspcva.mm"
include "cres.mm"
include "simpl.mm"
include "simplrl.mm"
include "simplrr.mm"
include "lindslinindimp2lem2.mm"
include "syl13anc.mm"
include "c0g.mm"
include "id.mm"
include "a1i.mm"
include "breq12d.mm"
include "eqeq2d.mm"
include "orbi12d.mm"
include "cvv.mm"
include "breq2i.mm"
include "biimpi.mm"
include "fvexd.mm"
include "fsuppres.mm"
include "pm2.24d.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cpw.mm"
include "simplr.mm"
include "fveq2i.mm"
include "eqtr2i.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "ssdifss.mm"
include "wb.mm"
include "difexg.mm"
include "elpwg.mm"
include "mpbird.mm"
include "lincval.mm"
include "syl3anc.mm"
include "fvres.mm"
include "oveq1d.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "w3a.mm"
include "3anass.mm"
include "lindslinindimp2lem4.mm"
include "3eqtrrd.mm"
include "jaoi.mm"
include "com23.mm"
include "mpcom.mm"
include "syl5.mm"
include "expd.mm"
include "syldc.mm"
include "pm2.61i.mm"

theorem lindslinindsimp2lem5
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let cM: class M
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vz: setvar z
  let vk: setvar k
  assume lindslinind.r: |- R = ( Scalar ` M )
  assume lindslinind.b: |- B = ( Base ` R )
  assume lindslinind.0: |- .0. = ( 0g ` R )
  assume lindslinind.z: |- Z = ( 0g ` M )

  disjoint B f
  disjoint B g
  disjoint B y
  disjoint f g
  disjoint f y
  disjoint g y
  disjoint M f
  disjoint M g
  disjoint M y
  disjoint R f
  disjoint R x
  disjoint f x
  disjoint S f
  disjoint S g
  disjoint S x
  disjoint S y
  disjoint g x
  disjoint x y
  disjoint V g
  disjoint V y
  disjoint Z f
  disjoint Z g
  disjoint Z y
  disjoint .0. f
  disjoint .0. g
  disjoint .0. x
  disjoint .0. y
  disjoint R g
  disjoint R y
  disjoint B s
  disjoint B z
  disjoint f s
  disjoint f z
  disjoint g s
  disjoint g z
  disjoint s y
  disjoint s z
  disjoint y z
  disjoint M s
  disjoint M z
  disjoint R z
  disjoint x z
  disjoint S s
  disjoint S z
  disjoint s x
  disjoint V s
  disjoint V z
  disjoint Z s
  disjoint .0. s
  disjoint .0. z
  disjoint Z z
  disjoint k x
  assert |- ( ( ( S e. V /\ M e. LMod ) /\ ( S C_ ( Base ` M ) /\ x e. S ) ) -> ( ( f e. ( B ^m S ) /\ ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z ) ) -> ( A. y e. ( B \ { .0. } ) A. g e. ( B ^m ( S \ { x } ) ) ( -. g finSupp .0. \/ -. ( y ( .s ` M ) x ) = ( g ( linC ` M ) ( S \ { x } ) ) ) -> ( f ` x ) = .0. ) ) )

  proof
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    c.0
    wceq
    #
    cS
    cV
    wcel
    #
    cM
    clmod
    wcel
    #
    wa
    #
    cS
    cM
    cbs
    cfv
    #
    wss
    #
    @0
    cS
    wcel
    #
    wa
    #
    wa
    #
    @1
    cB
    cS
    cmap
    co
    wcel
    #
    @1
    c.0
    cfsupp
    wbr
    #
    @1
    cS
    cM
    clinc
    cfv
    #
    co
    cZ
    wceq
    #
    wa
    #
    wa
    #
    vg
    cv
    #
    c.0
    cfsupp
    wbr
    #
    wn
    #
    vy
    cv
    #
    @0
    cM
    cvsca
    cfv
    #
    co
    #
    @18
    cS
    @0
    csn
    #
    cdif
    #
    @14
    co
    #
    wceq
    #
    wn
    #
    wo
    #
    vg
    cB
    @25
    cmap
    co
    #
    wral
    #
    vy
    cB
    c.0
    csn
    cdif
    #
    wral
    #
    @3
    wi
    #
    wi
    wi
    @3
    @34
    @11
    @17
    @3
    @33
    ax-1
    2a1d
    @3
    wn
    #
    @11
    @17
    @34
    @11
    @17
    wa
    #
    @35
    @2
    cR
    cminusg
    cfv
    #
    cfv
    #
    @32
    wcel
    #
    @34
    @36
    @35
    @2
    @32
    wcel
    #
    @39
    @36
    @2
    c.0
    wne
    #
    @2
    cB
    wcel
    #
    @41
    wa
    @35
    @40
    @36
    @42
    @41
    @17
    @11
    @42
    @12
    @11
    @42
    wi
    #
    @16
    @12
    cS
    cB
    @1
    wf
    #
    @43
    @1
    cB
    cS
    elmapi
    @11
    @44
    @42
    @10
    @44
    @42
    wi
    #
    @6
    @9
    @45
    @8
    @44
    @9
    @42
    cS
    cB
    @0
    @1
    ffvelrn
    expcom
    adantl
    adantl
    com12
    syl
    adantr
    impcom
    biantrurd
    @41
    @35
    @2
    c.0
    df-ne
    bicomi
    @2
    cB
    c.0
    eldifsn
    3bitr4g
    @36
    @40
    @39
    @36
    cR
    cgrp
    wcel
    #
    @40
    @39
    @11
    @46
    @17
    @6
    @46
    @10
    @5
    @46
    @4
    cR
    cM
    lindslinind.r
    lmodfgrp
    adantl
    adantr
    adantr
    cB
    cR
    @37
    @2
    c.0
    lindslinind.b
    lindslinind.0
    @37
    eqid
    grpinvnzcl
    sylan
    ex
    sylbid
    @36
    @39
    @33
    @3
    @39
    @33
    wa
    @20
    @38
    @0
    @22
    co
    #
    @26
    wceq
    #
    wn
    #
    wo
    #
    vg
    @30
    wral
    #
    @36
    @3
    @31
    @51
    vy
    @38
    @32
    @21
    @38
    wceq
    #
    @29
    @50
    vg
    @30
    @52
    @28
    @49
    @20
    @52
    @27
    @48
    @52
    @23
    @47
    @26
    @21
    @38
    @0
    @22
    oveq1
    eqeq1d
    notbid
    orbi2d
    ralbidv
    rspcva
    @1
    @25
    cres
    #
    @30
    wcel
    #
    @36
    @51
    @3
    wi
    @36
    @6
    @8
    @9
    @12
    @54
    @11
    @6
    @17
    @6
    @10
    simpl
    adantr
    #
    @6
    @8
    @9
    @17
    simplrl
    @6
    @8
    @9
    @17
    simplrr
    @17
    @12
    @11
    @12
    @16
    simpl
    adantl
    vx
    cB
    cR
    cS
    vf
    @53
    cM
    cV
    @38
    c.0
    cZ
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    @38
    eqid
    #
    @53
    eqid
    #
    lindslinindimp2lem2
    syl13anc
    #
    @54
    @51
    @36
    @3
    @54
    @51
    @36
    @3
    wi
    #
    @54
    @51
    wa
    @53
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    wn
    #
    @47
    @53
    @25
    @14
    co
    #
    wceq
    #
    wn
    #
    wo
    #
    @59
    @50
    @66
    vg
    @53
    @30
    @18
    @53
    wceq
    #
    @20
    @62
    @49
    @65
    @67
    @19
    @61
    @67
    @18
    @53
    c.0
    @60
    cfsupp
    @67
    id
    c.0
    @60
    wceq
    @67
    lindslinind.0
    a1i
    breq12d
    notbid
    @67
    @48
    @64
    @67
    @26
    @63
    @47
    @18
    @53
    @25
    @14
    oveq1
    eqeq2d
    notbid
    orbi12d
    rspcva
    @62
    @59
    @65
    @36
    @62
    @3
    @36
    @61
    @3
    @36
    @1
    cvv
    @25
    @60
    @17
    @1
    @60
    cfsupp
    wbr
    #
    @11
    @16
    @68
    @12
    @13
    @68
    @15
    @13
    @68
    c.0
    @60
    @1
    cfsupp
    lindslinind.0
    breq2i
    biimpi
    adantr
    adantl
    adantl
    @36
    cR
    c0g
    fvexd
    fsuppres
    pm2.24d
    com12
    @36
    @65
    @3
    @36
    @64
    @3
    @36
    @63
    cM
    vz
    @25
    vz
    cv
    #
    @53
    cfv
    #
    @69
    @22
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cM
    vz
    @25
    @69
    @1
    cfv
    #
    @69
    @22
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @47
    @36
    @5
    @53
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @25
    cmap
    co
    #
    wcel
    @25
    @7
    cpw
    wcel
    #
    @63
    @73
    wceq
    @11
    @5
    @17
    @4
    @5
    @10
    simplr
    adantr
    @36
    @53
    @30
    @80
    @58
    @79
    cB
    @25
    cmap
    cB
    cR
    cbs
    cfv
    @79
    lindslinind.b
    cR
    @78
    cbs
    lindslinind.r
    fveq2i
    eqtr2i
    oveq1i
    syl6eleqr
    @11
    @81
    @17
    @11
    @81
    @25
    @7
    wss
    #
    @10
    @82
    @6
    @8
    @82
    @9
    cS
    @7
    @24
    ssdifss
    adantr
    adantl
    @11
    @25
    cvv
    wcel
    #
    @81
    @82
    wb
    @6
    @83
    @10
    @4
    @83
    @5
    cS
    @24
    cV
    difexg
    adantr
    adantr
    @25
    @7
    cvv
    elpwg
    syl
    mpbird
    adantr
    vz
    @53
    cM
    @25
    clmod
    lincval
    syl3anc
    @36
    @72
    @76
    cM
    cgsu
    @36
    vz
    @25
    @71
    @75
    @36
    @69
    @25
    wcel
    #
    wa
    @70
    @74
    @69
    @22
    @84
    @70
    @74
    wceq
    @36
    @69
    @25
    @1
    fvres
    adantl
    oveq1d
    mpteq2dva
    oveq2d
    @36
    @6
    @10
    @12
    @13
    @15
    w3a
    #
    @77
    @47
    wceq
    @55
    @6
    @10
    @17
    simplr
    @17
    @85
    @11
    @17
    @85
    @85
    @17
    @12
    @13
    @15
    3anass
    bicomi
    biimpi
    adantl
    vx
    vz
    cB
    cR
    cS
    vf
    @53
    cM
    cV
    @38
    c.0
    cZ
    lindslinind.r
    lindslinind.b
    lindslinind.0
    lindslinind.z
    @56
    @57
    lindslinindimp2lem4
    syl3anc
    3eqtrrd
    pm2.24d
    com12
    jaoi
    syl
    ex
    com23
    mpcom
    syl5
    expd
    syldc
    expd
    pm2.61i
end

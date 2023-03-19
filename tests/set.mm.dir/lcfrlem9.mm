include "csn.mm"
include "cdif.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "co.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fnmpti.mm"
include "a1i.mm"
include "wcel.mm"
include "wb.mm"
include "fvelrnb.mm"
include "syl.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "lcfrlem8.mm"
include "wne.mm"
include "wo.mm"
include "eqid.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "rexeqbidv.mm"
include "riotabidv.mm"
include "mpteq2dv.mm"
include "rspcev.mm"
include "sylancl.mm"
include "olcd.mm"
include "dochflcl.mm"
include "lcfl6.mm"
include "mpbird.mm"
include "dochsnkr2cl.mm"
include "dochsnkrlem3.mm"
include "dochsnkrlem1.mm"
include "eqnetrrd.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lkr0f2.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "wn.mm"
include "simprl.mm"
include "lcfl1lem.mm"
include "simplbi.mm"
include "adantl.mm"
include "biimprd.mm"
include "impr.mm"
include "neneqd.mm"
include "biimpa.mm"
include "ord.mm"
include "3impia.mm"
include "mpd3an23.mm"
include "sylan2b.mm"
include "eqcom.mm"
include "ad2antrr.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "ex.mm"
include "impbid.mm"
include "bitrd.mm"
include "eqrdv.mm"
include "simplrl.mm"
include "simplrr.mm"
include "3eqtr3d.mm"
include "lcfl7lem.mm"
include "ralrimivva.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"

theorem lcfrlem9
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vy: setvar y
  let vg: setvar g
  let vt: setvar t
  let vu: setvar u
  let vz: setvar z
  let cX: class X
  assume lcf1o.h: |- H = ( LHyp ` K )
  assume lcf1o.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcf1o.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcf1o.v: |- V = ( Base ` U )
  assume lcf1o.a: |- .+ = ( +g ` U )
  assume lcf1o.t: |- .x. = ( .s ` U )
  assume lcf1o.s: |- S = ( Scalar ` U )
  assume lcf1o.r: |- R = ( Base ` S )
  assume lcf1o.z: |- .0. = ( 0g ` U )
  assume lcf1o.f: |- F = ( LFnl ` U )
  assume lcf1o.l: |- L = ( LKer ` U )
  assume lcf1o.d: |- D = ( LDual ` U )
  assume lcf1o.q: |- Q = ( 0g ` D )
  assume lcf1o.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcf1o.j: |- J = ( x e. ( V \ { .0. } ) |-> ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) )
  assume lcflo.k: |- ( ph -> ( K e. HL /\ W e. H ) )

  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint .+ f
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint .+ k
  disjoint v w
  disjoint v x
  disjoint .+ v
  disjoint w x
  disjoint .+ w
  disjoint .+ x
  disjoint J k
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint C k
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint F f
  disjoint L f
  disjoint L k
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint ._|_ f
  disjoint ._|_ k
  disjoint ._|_ v
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint Q k
  disjoint Q v
  disjoint Q w
  disjoint Q x
  disjoint R f
  disjoint R k
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint S k
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint .x. f
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .x. x
  disjoint U k
  disjoint U w
  disjoint U x
  disjoint V f
  disjoint V k
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint .0. k
  disjoint .0. v
  disjoint .0. w
  disjoint .0. x
  disjoint k ph
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .0. x
  disjoint v x
  disjoint V v
  disjoint V x
  disjoint .x. x
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint v w
  disjoint .+ x
  disjoint R x
  disjoint f y
  disjoint k y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint .+ y
  disjoint g k
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g z
  disjoint J g
  disjoint k t
  disjoint k u
  disjoint k z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint J t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint J u
  disjoint v z
  disjoint w z
  disjoint x z
  disjoint J z
  disjoint g y
  disjoint C g
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint f z
  disjoint L y
  disjoint L z
  disjoint ._|_ y
  disjoint ._|_ z
  disjoint Q g
  disjoint Q z
  disjoint R y
  disjoint S y
  disjoint S z
  disjoint .x. y
  disjoint U y
  disjoint U z
  disjoint f t
  disjoint f u
  disjoint t y
  disjoint V t
  disjoint u y
  disjoint V u
  disjoint V y
  disjoint V z
  disjoint .0. t
  disjoint .0. u
  disjoint .0. y
  disjoint .0. z
  disjoint g ph
  disjoint ph t
  disjoint ph u
  disjoint ph y
  disjoint ph z
  disjoint f g
  disjoint X k
  disjoint X v
  disjoint X w
  disjoint X x
  assert |- ( ph -> J : ( V \ { .0. } ) -1-1-onto-> ( C \ { Q } ) )

  proof
    wph
    cJ
    cV
    c.0
    csn
    cdif
    #
    wfn
    #
    cJ
    crn
    #
    cC
    cQ
    csn
    cdif
    #
    wceq
    vt
    cv
    #
    cJ
    cfv
    #
    vu
    cv
    #
    cJ
    cfv
    #
    wceq
    #
    vt
    vu
    weq
    #
    wi
    #
    vu
    @0
    wral
    vt
    @0
    wral
    @0
    @3
    cJ
    wf1o
    @1
    wph
    vx
    @0
    vv
    cV
    vv
    cv
    #
    vw
    cv
    #
    vk
    cv
    #
    vx
    cv
    #
    c.x
    co
    c.pl
    co
    wceq
    vw
    @14
    csn
    c.pe
    cfv
    wrex
    vk
    cR
    crio
    #
    cmpt
    cJ
    vv
    cV
    @15
    cV
    cU
    cbs
    cfv
    cvv
    lcf1o.v
    cU
    cbs
    fvex
    eqeltri
    mptex
    lcf1o.j
    fnmpti
    a1i
    #
    wph
    vg
    @2
    @3
    wph
    vg
    cv
    #
    @2
    wcel
    #
    vz
    cv
    #
    cJ
    cfv
    #
    @17
    wceq
    #
    vz
    @0
    wrex
    #
    @17
    @3
    wcel
    #
    wph
    @1
    @18
    @22
    wb
    @16
    vz
    @0
    @17
    cJ
    fvelrnb
    syl
    wph
    @22
    @23
    wph
    @21
    @23
    vz
    @0
    wph
    @19
    @0
    wcel
    #
    wa
    #
    @20
    @3
    wcel
    @21
    @23
    @25
    @20
    vv
    cV
    @11
    @12
    @13
    @19
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @19
    csn
    #
    c.pe
    cfv
    #
    wrex
    #
    vk
    cR
    crio
    #
    cmpt
    #
    @3
    @25
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    @19
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @24
    lcflo.k
    adantr
    #
    wph
    @24
    simpr
    #
    lcfrlem8
    @25
    @33
    cC
    wcel
    #
    @33
    cQ
    wne
    #
    @33
    @3
    wcel
    @25
    @37
    @33
    cL
    cfv
    #
    cV
    wceq
    #
    @33
    vv
    cV
    @11
    @12
    @13
    vy
    cv
    #
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @41
    csn
    #
    c.pe
    cfv
    #
    wrex
    #
    vk
    cR
    crio
    #
    cmpt
    #
    wceq
    #
    vy
    @0
    wrex
    #
    wo
    @25
    @51
    @40
    @25
    @24
    @33
    @33
    wceq
    #
    @51
    @36
    @33
    eqid
    #
    @50
    @52
    vy
    @19
    @0
    vy
    vz
    weq
    #
    @49
    @33
    @33
    @54
    vv
    cV
    @48
    @32
    @54
    @47
    @31
    vk
    cR
    @54
    @44
    @28
    vw
    @46
    @30
    @54
    @45
    @29
    c.pe
    @41
    @19
    sneq
    fveq2d
    @54
    @43
    @27
    @11
    @54
    @42
    @26
    @12
    c.pl
    @41
    @19
    @13
    c.x
    oveq2
    oveq2d
    eqeq2d
    rexeqbidv
    riotabidv
    mpteq2dv
    eqeq2d
    rspcev
    sylancl
    olcd
    @25
    vy
    vw
    vv
    cC
    c.pl
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    @33
    cH
    cK
    cL
    c.pe
    cV
    cW
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.c
    @35
    @25
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    cF
    @33
    cH
    cK
    c.pe
    cV
    cW
    @19
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.z
    lcf1o.a
    lcf1o.t
    lcf1o.f
    lcf1o.s
    lcf1o.r
    @53
    @35
    @36
    dochflcl
    #
    lcfl6
    mpbird
    @25
    @39
    cV
    wne
    @38
    @25
    @39
    c.pe
    cfv
    c.pe
    cfv
    @39
    cV
    @25
    cU
    cF
    @33
    cH
    cK
    cL
    c.pe
    cV
    cW
    @19
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.z
    lcf1o.f
    lcf1o.l
    @35
    @55
    @25
    vw
    vv
    cS
    c.pl
    cR
    c.x
    cU
    vk
    @33
    cH
    cK
    cL
    c.pe
    cV
    cW
    @19
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.z
    lcf1o.a
    lcf1o.t
    lcf1o.l
    lcf1o.s
    lcf1o.r
    @53
    @35
    @36
    dochsnkr2cl
    #
    dochsnkrlem3
    @25
    cU
    cF
    @33
    cH
    cK
    cL
    c.pe
    cV
    cW
    @19
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.z
    lcf1o.f
    lcf1o.l
    @35
    @55
    @56
    dochsnkrlem1
    eqnetrrd
    @25
    @39
    cV
    @33
    cQ
    @25
    cD
    cF
    @33
    cL
    cV
    cU
    cQ
    lcf1o.v
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    wph
    cU
    clmod
    wcel
    #
    @24
    wph
    cU
    cH
    cK
    cW
    lcf1o.h
    lcf1o.u
    lcflo.k
    dvhlmod
    #
    adantr
    @55
    lkr0f2
    necon3bid
    mpbid
    @33
    cC
    cQ
    eldifsn
    sylanbrc
    eqeltrd
    @20
    @17
    @3
    eleq1
    syl5ibcom
    rexlimdva
    wph
    @23
    @22
    wph
    @23
    wa
    #
    @22
    @17
    @33
    wceq
    #
    vz
    @0
    wrex
    #
    @23
    wph
    @17
    cC
    wcel
    #
    @17
    cQ
    wne
    #
    wa
    #
    @61
    @17
    cC
    cQ
    eldifsn
    wph
    @64
    wa
    #
    @62
    @17
    cL
    cfv
    #
    cV
    wceq
    #
    wn
    #
    @61
    wph
    @62
    @63
    simprl
    @65
    @66
    cV
    wph
    @62
    @63
    @66
    cV
    wne
    #
    wph
    @62
    wa
    #
    @69
    @63
    @70
    @66
    cV
    @17
    cQ
    @70
    cD
    cF
    @17
    cL
    cV
    cU
    cQ
    lcf1o.v
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    wph
    @57
    @62
    @58
    adantr
    @62
    @17
    cF
    wcel
    #
    wph
    @62
    @71
    @66
    c.pe
    cfv
    c.pe
    cfv
    @66
    wceq
    cC
    vf
    cF
    @17
    cL
    c.pe
    lcf1o.c
    lcfl1lem
    simplbi
    #
    adantl
    lkr0f2
    necon3bid
    biimprd
    impr
    neneqd
    @65
    @62
    @68
    @61
    @65
    @62
    wa
    @67
    @61
    @65
    @62
    @67
    @61
    wo
    @65
    vz
    vw
    vv
    cC
    c.pl
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    @17
    cH
    cK
    cL
    c.pe
    cV
    cW
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.c
    wph
    @34
    @64
    lcflo.k
    adantr
    @64
    @71
    wph
    @62
    @71
    @63
    @72
    adantr
    adantl
    lcfl6
    biimpa
    ord
    3impia
    mpd3an23
    sylan2b
    @59
    @21
    @60
    vz
    @0
    @21
    @17
    @20
    wceq
    @59
    @24
    wa
    #
    @60
    @20
    @17
    eqcom
    @73
    @20
    @33
    @17
    @73
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    @19
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    wph
    @34
    @23
    @24
    lcflo.k
    ad2antrr
    @59
    @24
    simpr
    lcfrlem8
    eqeq2d
    syl5bb
    rexbidva
    mpbird
    ex
    impbid
    bitrd
    eqrdv
    wph
    @10
    vt
    vu
    @0
    @0
    wph
    @4
    @0
    wcel
    #
    @6
    @0
    wcel
    #
    wa
    #
    wa
    #
    @8
    @9
    @77
    @8
    wa
    #
    vw
    vv
    c.pl
    cR
    cS
    c.x
    cU
    vk
    cF
    vv
    cV
    @11
    @12
    @13
    @4
    c.x
    co
    c.pl
    co
    wceq
    vw
    @4
    csn
    c.pe
    cfv
    wrex
    vk
    cR
    crio
    cmpt
    #
    cH
    vv
    cV
    @11
    @12
    @13
    @6
    c.x
    co
    c.pl
    co
    wceq
    vw
    @6
    csn
    c.pe
    cfv
    wrex
    vk
    cR
    crio
    cmpt
    #
    cK
    cL
    c.pe
    cV
    cW
    @4
    @6
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    wph
    @34
    @76
    @8
    lcflo.k
    ad2antrr
    #
    @79
    eqid
    @80
    eqid
    wph
    @74
    @75
    @8
    simplrl
    #
    wph
    @74
    @75
    @8
    simplrr
    #
    @78
    @5
    @7
    @79
    @80
    @77
    @8
    simpr
    @78
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    @4
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    @81
    @82
    lcfrlem8
    @78
    vx
    vw
    vv
    cC
    cD
    c.pl
    cQ
    cR
    cS
    c.x
    cU
    vf
    vk
    cF
    cH
    cJ
    cK
    cL
    c.pe
    cV
    cW
    @6
    c.0
    lcf1o.h
    lcf1o.o
    lcf1o.u
    lcf1o.v
    lcf1o.a
    lcf1o.t
    lcf1o.s
    lcf1o.r
    lcf1o.z
    lcf1o.f
    lcf1o.l
    lcf1o.d
    lcf1o.q
    lcf1o.c
    lcf1o.j
    @81
    @83
    lcfrlem8
    3eqtr3d
    lcfl7lem
    ex
    ralrimivva
    vt
    vu
    @0
    @3
    cJ
    dff1o6
    syl3anbrc
end

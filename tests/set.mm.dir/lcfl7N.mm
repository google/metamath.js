include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "csn.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "cdif.mm"
include "wo.mm"
include "wreu.mm"
include "lcfl6.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvriotav.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "lcfl7lem.mm"
include "ex.mm"
include "ralrimivva.mm"
include "a1d.mm"
include "ancld.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "rexeqbidv.mm"
include "mpteq2dv.mm"
include "reu4.mm"
include "syl6ibr.mm"
include "reurex.mm"
include "impbid1.mm"
include "orbi2d.mm"
include "bitrd.mm"

theorem lcfl7N
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vl: setvar l
  let vu: setvar u
  let vy: setvar y
  let vz: setvar z
  assume lcfl6.h: |- H = ( LHyp ` K )
  assume lcfl6.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume lcfl6.u: |- U = ( ( DVecH ` K ) ` W )
  assume lcfl6.v: |- V = ( Base ` U )
  assume lcfl6.a: |- .+ = ( +g ` U )
  assume lcfl6.t: |- .x. = ( .s ` U )
  assume lcfl6.s: |- S = ( Scalar ` U )
  assume lcfl6.r: |- R = ( Base ` S )
  assume lcfl6.z: |- .0. = ( 0g ` U )
  assume lcfl6.f: |- F = ( LFnl ` U )
  assume lcfl6.l: |- L = ( LKer ` U )
  assume lcfl6.c: |- C = { f e. F | ( ._|_ ` ( ._|_ ` ( L ` f ) ) ) = ( L ` f ) }
  assume lcfl6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume lcfl6.g: |- ( ph -> G e. F )

  disjoint k v
  disjoint k w
  disjoint .+ k
  disjoint v w
  disjoint .+ v
  disjoint .+ w
  disjoint f k
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint ._|_ f
  disjoint k x
  disjoint ._|_ k
  disjoint v x
  disjoint ._|_ v
  disjoint w x
  disjoint ._|_ w
  disjoint ._|_ x
  disjoint .0. w
  disjoint .0. x
  disjoint C x
  disjoint G f
  disjoint G x
  disjoint F f
  disjoint L f
  disjoint L x
  disjoint ph x
  disjoint R k
  disjoint R v
  disjoint S k
  disjoint S w
  disjoint S x
  disjoint V v
  disjoint V x
  disjoint U x
  disjoint .x. k
  disjoint .x. v
  disjoint .x. w
  disjoint .+ x
  disjoint R x
  disjoint .x. x
  disjoint k l
  disjoint k u
  disjoint k y
  disjoint k z
  disjoint l u
  disjoint l v
  disjoint l w
  disjoint l y
  disjoint l z
  disjoint u v
  disjoint u w
  disjoint u y
  disjoint u z
  disjoint v y
  disjoint v z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint l x
  disjoint .+ l
  disjoint u x
  disjoint .+ u
  disjoint x y
  disjoint x z
  disjoint .+ y
  disjoint .+ z
  disjoint G y
  disjoint ph y
  disjoint S l
  disjoint S z
  disjoint ._|_ l
  disjoint ._|_ u
  disjoint ._|_ y
  disjoint ._|_ z
  disjoint .0. y
  disjoint .0. z
  disjoint R l
  disjoint R u
  disjoint R y
  disjoint .x. l
  disjoint .x. u
  disjoint .x. y
  disjoint .x. z
  disjoint U l
  disjoint U z
  disjoint V u
  disjoint V y
  assert |- ( ph -> ( G e. C <-> ( ( L ` G ) = V \/ E! x e. ( V \ { .0. } ) G = ( v e. V |-> ( iota_ k e. R E. w e. ( ._|_ ` { x } ) v = ( w .+ ( k .x. x ) ) ) ) ) ) )

  proof
    wph
    cG
    cC
    wcel
    cG
    cL
    cfv
    cV
    wceq
    #
    cG
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
    #
    c.pl
    co
    #
    wceq
    #
    vw
    @4
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
    vx
    cV
    c.0
    csn
    cdif
    #
    wrex
    #
    wo
    @0
    @13
    vx
    @14
    wreu
    #
    wo
    wph
    vx
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
    cG
    cH
    cK
    cL
    c.pe
    cV
    cW
    c.0
    lcfl6.h
    lcfl6.o
    lcfl6.u
    lcfl6.v
    lcfl6.a
    lcfl6.t
    lcfl6.s
    lcfl6.r
    lcfl6.z
    lcfl6.f
    lcfl6.l
    lcfl6.c
    lcfl6.k
    lcfl6.g
    lcfl6
    wph
    @15
    @16
    @0
    wph
    @15
    @16
    wph
    @15
    @15
    @13
    cG
    vv
    cV
    @1
    @2
    @3
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
    @17
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
    wa
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @14
    wral
    vx
    @14
    wral
    #
    wa
    @16
    wph
    @15
    @30
    wph
    @30
    @15
    wph
    @29
    vx
    vy
    @14
    @14
    wph
    @4
    @14
    wcel
    #
    @17
    @14
    wcel
    #
    wa
    #
    wa
    #
    @27
    @28
    @34
    @27
    wa
    #
    vz
    vu
    c.pl
    cR
    cS
    c.x
    cU
    vl
    cF
    vu
    cV
    vu
    cv
    #
    vz
    cv
    #
    vl
    cv
    #
    @4
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    @9
    wrex
    #
    vl
    cR
    crio
    #
    cmpt
    #
    cH
    vu
    cV
    @36
    @37
    @38
    @17
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    @22
    wrex
    #
    vl
    cR
    crio
    #
    cmpt
    #
    cK
    cL
    c.pe
    cV
    cW
    @4
    @17
    c.0
    lcfl6.h
    lcfl6.o
    lcfl6.u
    lcfl6.v
    lcfl6.a
    lcfl6.t
    lcfl6.s
    lcfl6.r
    lcfl6.z
    lcfl6.f
    lcfl6.l
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @33
    @27
    lcfl6.k
    ad2antrr
    @44
    eqid
    @50
    eqid
    wph
    @31
    @32
    @27
    simplrl
    wph
    @31
    @32
    @27
    simplrr
    @35
    cG
    @44
    @50
    @35
    cG
    @12
    @44
    @34
    @13
    @26
    simprl
    vv
    vu
    cV
    @11
    @43
    vv
    vu
    weq
    #
    @11
    @36
    @6
    wceq
    #
    vw
    @9
    wrex
    #
    vk
    cR
    crio
    @43
    @51
    @10
    @53
    vk
    cR
    @51
    @7
    @52
    vw
    @9
    @1
    @36
    @6
    eqeq1
    rexbidv
    riotabidv
    @53
    @42
    vk
    vl
    cR
    vk
    vl
    weq
    #
    @53
    @36
    @2
    @39
    c.pl
    co
    #
    wceq
    #
    vw
    @9
    wrex
    @42
    @54
    @52
    @56
    vw
    @9
    @54
    @6
    @55
    @36
    @54
    @5
    @39
    @2
    c.pl
    @3
    @38
    @4
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    @56
    @41
    vw
    vz
    @9
    vw
    vz
    weq
    #
    @55
    @40
    @36
    @2
    @37
    @39
    c.pl
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    cbvriotav
    syl6eq
    cbvmptv
    syl6eq
    @35
    cG
    @25
    @50
    @34
    @13
    @26
    simprr
    vv
    vu
    cV
    @24
    @49
    @51
    @24
    @36
    @19
    wceq
    #
    vw
    @22
    wrex
    #
    vk
    cR
    crio
    @49
    @51
    @23
    @59
    vk
    cR
    @51
    @20
    @58
    vw
    @22
    @1
    @36
    @19
    eqeq1
    rexbidv
    riotabidv
    @59
    @48
    vk
    vl
    cR
    @54
    @59
    @36
    @2
    @45
    c.pl
    co
    #
    wceq
    #
    vw
    @22
    wrex
    @48
    @54
    @58
    @61
    vw
    @22
    @54
    @19
    @60
    @36
    @54
    @18
    @45
    @2
    c.pl
    @3
    @38
    @17
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    @61
    @47
    vw
    vz
    @22
    @57
    @60
    @46
    @36
    @2
    @37
    @45
    c.pl
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    cbvriotav
    syl6eq
    cbvmptv
    syl6eq
    eqtr3d
    lcfl7lem
    ex
    ralrimivva
    a1d
    ancld
    @13
    @26
    vx
    vy
    @14
    @28
    @12
    @25
    cG
    @28
    vv
    cV
    @11
    @24
    @28
    @10
    @23
    vk
    cR
    @28
    @7
    @20
    vw
    @9
    @22
    @28
    @8
    @21
    c.pe
    @4
    @17
    sneq
    fveq2d
    @28
    @6
    @19
    @1
    @28
    @5
    @18
    @2
    c.pl
    @4
    @17
    @3
    c.x
    oveq2
    oveq2d
    eqeq2d
    rexeqbidv
    riotabidv
    mpteq2dv
    eqeq2d
    reu4
    syl6ibr
    @13
    vx
    @14
    reurex
    impbid1
    orbi2d
    bitrd
end

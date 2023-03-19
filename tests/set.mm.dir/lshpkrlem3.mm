include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cfv.mm"
include "wsbc.mm"
include "crio.mm"
include "wreu.mm"
include "lshpsmreu.mm"
include "riotasbc.mm"
include "syl.mm"
include "wcel.mm"
include "wb.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "cmpt.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvriotav.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "dfsbcq.mm"
include "3syl.mm"
include "mpbird.mm"
include "fvex.mm"
include "sbcie.mm"
include "sylib.mm"

theorem lshpkrlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vb: setvar b
  let vl: setvar l
  assume lshpkrlem.v: |- V = ( Base ` W )
  assume lshpkrlem.a: |- .+ = ( +g ` W )
  assume lshpkrlem.n: |- N = ( LSpan ` W )
  assume lshpkrlem.p: |- .(+) = ( LSSum ` W )
  assume lshpkrlem.h: |- H = ( LSHyp ` W )
  assume lshpkrlem.w: |- ( ph -> W e. LVec )
  assume lshpkrlem.u: |- ( ph -> U e. H )
  assume lshpkrlem.z: |- ( ph -> Z e. V )
  assume lshpkrlem.x: |- ( ph -> X e. V )
  assume lshpkrlem.e: |- ( ph -> ( U .(+) ( N ` { Z } ) ) = V )
  assume lshpkrlem.d: |- D = ( Scalar ` W )
  assume lshpkrlem.k: |- K = ( Base ` D )
  assume lshpkrlem.t: |- .x. = ( .s ` W )
  assume lshpkrlem.o: |- .0. = ( 0g ` D )
  assume lshpkrlem.g: |- G = ( x e. V |-> ( iota_ k e. K E. y e. U x = ( y .+ ( k .x. Z ) ) ) )

  disjoint k x
  disjoint k y
  disjoint .+ k
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint K k
  disjoint K x
  disjoint .0. k
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint U k
  disjoint U x
  disjoint U y
  disjoint V x
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint Z k
  disjoint Z x
  disjoint Z y
  disjoint .+ z
  disjoint G z
  disjoint U z
  disjoint X z
  disjoint Z z
  disjoint k z
  disjoint x z
  disjoint y z
  disjoint .x. z
  disjoint b k
  disjoint b x
  disjoint b y
  disjoint .+ b
  disjoint .0. b
  disjoint .x. b
  disjoint U b
  disjoint X b
  disjoint Z b
  disjoint b ph
  disjoint l z
  disjoint .+ l
  disjoint G l
  disjoint K l
  disjoint U l
  disjoint X l
  disjoint Z l
  disjoint k l
  disjoint l x
  disjoint l y
  disjoint .x. l
  assert |- ( ph -> E. z e. U X = ( z .+ ( ( G ` X ) .x. Z ) ) )

  proof
    wph
    cX
    vz
    cv
    #
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
    vz
    cU
    wrex
    #
    vl
    cX
    cG
    cfv
    #
    wsbc
    #
    cX
    @0
    @6
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    cU
    wrex
    #
    wph
    @7
    @5
    vl
    @5
    vl
    cK
    crio
    #
    wsbc
    #
    wph
    @5
    vl
    cK
    wreu
    @13
    wph
    vz
    cD
    c.pl
    c.po
    c.x
    cU
    vl
    cH
    cK
    cN
    cV
    cW
    cX
    cZ
    lshpkrlem.v
    lshpkrlem.a
    lshpkrlem.n
    lshpkrlem.p
    lshpkrlem.h
    lshpkrlem.w
    lshpkrlem.u
    lshpkrlem.z
    lshpkrlem.x
    lshpkrlem.e
    lshpkrlem.d
    lshpkrlem.k
    lshpkrlem.t
    lshpsmreu
    @5
    vl
    cK
    riotasbc
    syl
    wph
    cX
    cV
    wcel
    @6
    @12
    wceq
    @7
    @13
    wb
    lshpkrlem.x
    vx
    cX
    vx
    cv
    #
    @3
    wceq
    #
    vz
    cU
    wrex
    #
    vl
    cK
    crio
    #
    @12
    cV
    cG
    @14
    cX
    wceq
    #
    @16
    @5
    vl
    cK
    @18
    @15
    @4
    vz
    cU
    @14
    cX
    @3
    eqeq1
    rexbidv
    riotabidv
    cG
    vx
    cV
    @14
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
    crio
    #
    cmpt
    vx
    cV
    @17
    cmpt
    lshpkrlem.g
    vx
    cV
    @25
    @17
    @24
    @16
    vk
    vl
    cK
    vk
    vl
    weq
    #
    @24
    @14
    @19
    @2
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    @16
    @26
    @23
    @28
    vy
    cU
    @26
    @22
    @27
    @14
    @26
    @21
    @2
    @19
    c.pl
    @20
    @1
    cZ
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    @28
    @15
    vy
    vz
    cU
    vy
    vz
    weq
    @27
    @3
    @14
    @19
    @0
    @2
    c.pl
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    cbvriotav
    mpteq2i
    eqtri
    @5
    vl
    cK
    riotaex
    fvmpt
    @5
    vl
    @6
    @12
    dfsbcq
    3syl
    mpbird
    @5
    @11
    vl
    @6
    cX
    cG
    fvex
    @1
    @6
    wceq
    #
    @4
    @10
    vz
    cU
    @29
    @3
    @9
    cX
    @29
    @2
    @8
    @0
    c.pl
    @1
    @6
    cZ
    c.x
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    sbcie
    sylib
end

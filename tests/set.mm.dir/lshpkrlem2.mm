include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "wcel.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "riotaex.mm"
include "fvmpt.mm"
include "syl.mm"
include "wreu.mm"
include "lshpsmreu.mm"
include "riotacl.mm"
include "eqeltrd.mm"

theorem lshpkrlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
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
  assert |- ( ph -> ( G ` X ) e. K )

  proof
    wph
    cX
    cG
    cfv
    #
    cX
    vy
    cv
    vk
    cv
    cZ
    c.x
    co
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
    cK
    wph
    cX
    cV
    wcel
    @0
    @4
    wceq
    lshpkrlem.x
    vx
    cX
    vx
    cv
    #
    @1
    wceq
    #
    vy
    cU
    wrex
    #
    vk
    cK
    crio
    @4
    cV
    cG
    @5
    cX
    wceq
    #
    @7
    @3
    vk
    cK
    @8
    @6
    @2
    vy
    cU
    @5
    cX
    @1
    eqeq1
    rexbidv
    riotabidv
    lshpkrlem.g
    @3
    vk
    cK
    riotaex
    fvmpt
    syl
    wph
    @3
    vk
    cK
    wreu
    @4
    cK
    wcel
    wph
    vy
    cD
    c.pl
    c.po
    c.x
    cU
    vk
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
    @3
    vk
    cK
    riotacl
    syl
    eqeltrd
end

include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "lsppr.mm"
include "eleq2d.mm"
include "cvv.mm"
include "id.mm"
include "ovex.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem lspprel
  let wph: wff ph
  let c.pl: class .+
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vl: setvar l
  let vv: setvar v
  assume lsppr.v: |- V = ( Base ` W )
  assume lsppr.a: |- .+ = ( +g ` W )
  assume lsppr.f: |- F = ( Scalar ` W )
  assume lsppr.k: |- K = ( Base ` F )
  assume lsppr.t: |- .x. = ( .s ` W )
  assume lsppr.n: |- N = ( LSpan ` W )
  assume lsppr.w: |- ( ph -> W e. LMod )
  assume lsppr.x: |- ( ph -> X e. V )
  assume lsppr.y: |- ( ph -> Y e. V )

  disjoint k l
  disjoint .+ k
  disjoint .+ l
  disjoint F k
  disjoint F l
  disjoint K k
  disjoint K l
  disjoint N k
  disjoint N l
  disjoint .x. k
  disjoint .x. l
  disjoint V k
  disjoint V l
  disjoint W k
  disjoint W l
  disjoint X k
  disjoint X l
  disjoint Y k
  disjoint Y l
  disjoint k ph
  disjoint l ph
  disjoint Z k
  disjoint Z l
  disjoint k v
  disjoint l v
  disjoint N v
  disjoint W v
  disjoint X v
  disjoint Y v
  disjoint ph v
  disjoint Z v
  disjoint .+ v
  disjoint .x. v
  disjoint K v
  assert |- ( ph -> ( Z e. ( N ` { X , Y } ) <-> E. k e. K E. l e. K Z = ( ( k .x. X ) .+ ( l .x. Y ) ) ) )

  proof
    wph
    cZ
    cX
    cY
    cpr
    cN
    cfv
    #
    wcel
    cZ
    vv
    cv
    #
    vk
    cv
    cX
    c.x
    co
    #
    vl
    cv
    cY
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vl
    cK
    wrex
    vk
    cK
    wrex
    #
    vv
    cab
    #
    wcel
    cZ
    @4
    wceq
    #
    vl
    cK
    wrex
    #
    vk
    cK
    wrex
    #
    wph
    @0
    @7
    cZ
    wph
    vv
    c.pl
    c.x
    vk
    cF
    cK
    cN
    cV
    cW
    cX
    cY
    vl
    lsppr.v
    lsppr.a
    lsppr.f
    lsppr.k
    lsppr.t
    lsppr.n
    lsppr.w
    lsppr.x
    lsppr.y
    lsppr
    eleq2d
    @6
    @10
    vv
    cZ
    @9
    cZ
    cvv
    wcel
    #
    vk
    cK
    @8
    @11
    vl
    cK
    @8
    cZ
    @4
    cvv
    @8
    id
    @2
    @3
    c.pl
    ovex
    syl6eqel
    rexlimivw
    rexlimivw
    @1
    cZ
    wceq
    @5
    @8
    vk
    vl
    cK
    cK
    @1
    cZ
    @4
    eqeq1
    2rexbidv
    elab3
    syl6bb
end

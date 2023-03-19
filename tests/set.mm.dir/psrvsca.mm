include "wcel.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "wceq.mm"
include "cv.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "oveq1d.mm"
include "oveq2.mm"
include "psrvscafval.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"

theorem psrvsca
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let vh: setvar h
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume psrvsca.s: |- S = ( I mPwSer R )
  assume psrvsca.n: |- .xb = ( .s ` S )
  assume psrvsca.k: |- K = ( Base ` R )
  assume psrvsca.b: |- B = ( Base ` S )
  assume psrvsca.m: |- .x. = ( .r ` R )
  assume psrvsca.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume psrvsca.x: |- ( ph -> X e. K )
  assume psrvsca.y: |- ( ph -> F e. B )

  disjoint I h
  disjoint f g
  disjoint f k
  disjoint f x
  disjoint B f
  disjoint g k
  disjoint g x
  disjoint B g
  disjoint k x
  disjoint B k
  disjoint B x
  disjoint F f
  disjoint F x
  disjoint f h
  disjoint f y
  disjoint I f
  disjoint g h
  disjoint g y
  disjoint I g
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint k y
  disjoint I k
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint K f
  disjoint K x
  disjoint X f
  disjoint X x
  disjoint D f
  disjoint D g
  disjoint D k
  disjoint D x
  disjoint D y
  disjoint R f
  disjoint R g
  disjoint R k
  disjoint R x
  disjoint .x. f
  disjoint .x. g
  disjoint .x. k
  disjoint .x. x
  disjoint .xb f
  disjoint .xb x
  assert |- ( ph -> ( X .xb F ) = ( ( D X. { X } ) oF .x. F ) )

  proof
    wph
    cX
    cK
    wcel
    cF
    cB
    wcel
    cX
    cF
    c.xb
    co
    cD
    cX
    csn
    #
    cxp
    #
    cF
    c.x
    cof
    #
    co
    #
    wceq
    psrvsca.x
    psrvsca.y
    vx
    vf
    cX
    cF
    cK
    cB
    cD
    vx
    cv
    #
    csn
    #
    cxp
    #
    vf
    cv
    #
    @2
    co
    @3
    c.xb
    @1
    @7
    @2
    co
    @4
    cX
    wceq
    #
    @6
    @1
    @7
    @2
    @8
    @5
    @0
    cD
    @4
    cX
    sneq
    xpeq2d
    oveq1d
    @7
    cF
    @1
    @2
    oveq2
    vx
    cB
    cD
    cR
    cS
    c.xb
    c.x
    vf
    vh
    cI
    cK
    psrvsca.s
    psrvsca.n
    psrvsca.k
    psrvsca.b
    psrvsca.m
    psrvsca.d
    psrvscafval
    @1
    cF
    @2
    ovex
    ovmpt2
    syl2anc
end

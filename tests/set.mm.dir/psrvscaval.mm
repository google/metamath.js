include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "psrvsca.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "psrelbas.mm"
include "ffnd.mm"
include "wa.mm"
include "eqidd.mm"
include "ofc1.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem psrvscaval
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
  let cY: class Y
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
  assume psrvscaval.y: |- ( ph -> Y e. D )

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
  assert |- ( ph -> ( ( X .xb F ) ` Y ) = ( X .x. ( F ` Y ) ) )

  proof
    wph
    cY
    cX
    cF
    c.xb
    co
    #
    cfv
    cY
    cD
    cX
    csn
    cxp
    cF
    c.x
    cof
    co
    #
    cfv
    #
    cX
    cY
    cF
    cfv
    #
    c.x
    co
    #
    wph
    cY
    @0
    @1
    wph
    cB
    cD
    cR
    cS
    c.xb
    c.x
    vh
    cF
    cI
    cK
    cX
    psrvsca.s
    psrvsca.n
    psrvsca.k
    psrvsca.b
    psrvsca.m
    psrvsca.d
    psrvsca.x
    psrvsca.y
    psrvsca
    fveq1d
    wph
    cY
    cD
    wcel
    #
    @2
    @4
    wceq
    psrvscaval.y
    wph
    cD
    cX
    @3
    c.x
    cF
    cvv
    cK
    cY
    cD
    cvv
    wcel
    wph
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vh
    cn0
    cI
    cmap
    co
    cD
    psrvsca.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    psrvsca.x
    wph
    cD
    cK
    cF
    wph
    cB
    cD
    cR
    cS
    vh
    cI
    cK
    cF
    psrvsca.s
    psrvsca.k
    psrvsca.d
    psrvsca.b
    psrvsca.y
    psrelbas
    ffnd
    wph
    @5
    wa
    @3
    eqidd
    ofc1
    mpdan
    eqtrd
end

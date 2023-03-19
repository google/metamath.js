include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "mplvsca.mm"
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
include "cbs.mm"
include "eqid.mm"
include "mplelf.mm"
include "ffnd.mm"
include "wa.mm"
include "eqidd.mm"
include "ofc1.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem mplvscaval
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let vh: setvar h
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  let cY: class Y
  assume mplvsca.p: |- P = ( I mPoly R )
  assume mplvsca.n: |- .xb = ( .s ` P )
  assume mplvsca.k: |- K = ( Base ` R )
  assume mplvsca.b: |- B = ( Base ` P )
  assume mplvsca.m: |- .x. = ( .r ` R )
  assume mplvsca.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume mplvsca.x: |- ( ph -> X e. K )
  assume mplvsca.f: |- ( ph -> F e. B )
  assume mplvscaval.y: |- ( ph -> Y e. D )

  disjoint I h
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
    cP
    cR
    c.xb
    c.x
    vh
    cF
    cI
    cK
    cX
    mplvsca.p
    mplvsca.n
    mplvsca.k
    mplvsca.b
    mplvsca.m
    mplvsca.d
    mplvsca.x
    mplvsca.f
    mplvsca
    fveq1d
    wph
    cY
    cD
    wcel
    #
    @2
    @4
    wceq
    mplvscaval.y
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
    mplvsca.d
    cn0
    cI
    cmap
    ovex
    rabex2
    a1i
    mplvsca.x
    wph
    cD
    cR
    cbs
    cfv
    #
    cF
    wph
    cB
    cD
    cP
    cR
    vh
    cI
    @6
    cF
    mplvsca.p
    @6
    eqid
    mplvsca.b
    mplvsca.d
    mplvsca.f
    mplelf
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

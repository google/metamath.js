include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "pwsvscafval.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "wf.mm"
include "wfn.mm"
include "eqid.mm"
include "pwselbas.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "eqidd.mm"
include "ofc1.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem pwsvscaval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume pwsvscaval.y: |- Y = ( R ^s I )
  assume pwsvscaval.b: |- B = ( Base ` Y )
  assume pwsvscaval.s: |- .x. = ( .s ` R )
  assume pwsvscaval.t: |- .xb = ( .s ` Y )
  assume pwsvscaval.f: |- F = ( Scalar ` R )
  assume pwsvscaval.k: |- K = ( Base ` F )
  assume pwsvscaval.r: |- ( ph -> R e. V )
  assume pwsvscaval.i: |- ( ph -> I e. W )
  assume pwsvscaval.a: |- ( ph -> A e. K )
  assume pwsvscaval.x: |- ( ph -> X e. B )
  assume pwsvscaval.j: |- ( ph -> J e. I )


  assert |- ( ph -> ( ( A .xb X ) ` J ) = ( A .x. ( X ` J ) ) )

  proof
    wph
    cJ
    cA
    cX
    c.xb
    co
    #
    cfv
    cJ
    cI
    cA
    csn
    cxp
    cX
    c.x
    cof
    co
    #
    cfv
    #
    cA
    cJ
    cX
    cfv
    #
    c.x
    co
    #
    wph
    cJ
    @0
    @1
    wph
    cA
    cB
    cR
    c.xb
    c.x
    cF
    cI
    cK
    cV
    cW
    cX
    cY
    pwsvscaval.y
    pwsvscaval.b
    pwsvscaval.s
    pwsvscaval.t
    pwsvscaval.f
    pwsvscaval.k
    pwsvscaval.r
    pwsvscaval.i
    pwsvscaval.a
    pwsvscaval.x
    pwsvscafval
    fveq1d
    wph
    cJ
    cI
    wcel
    #
    @2
    @4
    wceq
    pwsvscaval.j
    wph
    cI
    cA
    @3
    c.x
    cX
    cW
    cK
    cJ
    pwsvscaval.i
    pwsvscaval.a
    wph
    cI
    cR
    cbs
    cfv
    #
    cX
    wf
    cX
    cI
    wfn
    wph
    @6
    cR
    cI
    cB
    cV
    cX
    cY
    cW
    pwsvscaval.y
    @6
    eqid
    pwsvscaval.b
    pwsvscaval.r
    pwsvscaval.i
    pwsvscaval.x
    pwselbas
    cI
    @6
    cX
    ffn
    syl
    wph
    @5
    wa
    @3
    eqidd
    ofc1
    mpdan
    eqtrd
end

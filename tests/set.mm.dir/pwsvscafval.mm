include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "cvsca.mm"
include "cfv.mm"
include "cv.mm"
include "cmpt.mm"
include "cof.mm"
include "wcel.mm"
include "wceq.mm"
include "pwsval.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "csca.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wfn.mm"
include "fnconstg.mm"
include "syl.mm"
include "eleqtrd.mm"
include "prdsvscaval.mm"
include "wa.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "syl6eqr.mm"
include "mpteq2dva.mm"
include "adantr.mm"
include "fvexd.mm"
include "fconstmpt.mm"
include "pwselbas.mm"
include "feqmptd.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"

theorem pwsvscafval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cI: class I
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


  assert |- ( ph -> ( A .xb X ) = ( ( I X. { A } ) oF .x. X ) )

  proof
    wph
    cA
    cX
    c.xb
    co
    cA
    cX
    cF
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    cvsca
    cfv
    #
    co
    vx
    cI
    cA
    vx
    cv
    #
    cX
    cfv
    #
    @3
    @0
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cI
    cA
    csn
    cxp
    #
    cX
    c.x
    cof
    co
    #
    wph
    c.xb
    @2
    cA
    cX
    wph
    c.xb
    cY
    cvsca
    cfv
    @2
    pwsvscaval.t
    wph
    cY
    @1
    cvsca
    wph
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    cY
    @1
    wceq
    pwsvscaval.r
    pwsvscaval.i
    cR
    cF
    cI
    cV
    cW
    cY
    pwsvscaval.y
    pwsvscaval.f
    pwsval
    syl2anc
    #
    fveq2d
    syl5eq
    oveqd
    wph
    vx
    @1
    cbs
    cfv
    #
    @0
    cF
    @2
    cA
    cX
    cI
    cK
    cvv
    cW
    @1
    @1
    eqid
    @13
    eqid
    @2
    eqid
    pwsvscaval.k
    cF
    cvv
    wcel
    wph
    cF
    cR
    csca
    cfv
    cvv
    pwsvscaval.f
    cR
    csca
    fvex
    eqeltri
    a1i
    pwsvscaval.i
    wph
    @11
    @0
    cI
    wfn
    pwsvscaval.r
    cI
    cR
    cV
    fnconstg
    syl
    pwsvscaval.a
    wph
    cX
    cB
    @13
    pwsvscaval.x
    wph
    cB
    cY
    cbs
    cfv
    @13
    pwsvscaval.b
    wph
    cY
    @1
    cbs
    @12
    fveq2d
    syl5eq
    eleqtrd
    prdsvscaval
    wph
    @8
    vx
    cI
    cA
    @4
    c.x
    co
    #
    cmpt
    @10
    wph
    vx
    cI
    @7
    @14
    wph
    @3
    cI
    wcel
    #
    wa
    #
    @6
    c.x
    cA
    @4
    @16
    @6
    cR
    cvsca
    cfv
    c.x
    @16
    @5
    cR
    cvsca
    wph
    @11
    @15
    @5
    cR
    wceq
    pwsvscaval.r
    cI
    cR
    @3
    cV
    fvconst2g
    sylan
    fveq2d
    pwsvscaval.s
    syl6eqr
    oveqd
    mpteq2dva
    wph
    vx
    cI
    cA
    @4
    c.x
    @9
    cX
    cW
    cK
    cvv
    pwsvscaval.i
    wph
    cA
    cK
    wcel
    @15
    pwsvscaval.a
    adantr
    @16
    @3
    cX
    fvexd
    @9
    vx
    cI
    cA
    cmpt
    wceq
    wph
    vx
    cI
    cA
    fconstmpt
    a1i
    wph
    vx
    cI
    cR
    cbs
    cfv
    #
    cX
    wph
    @17
    cR
    cI
    cB
    cV
    cX
    cY
    cW
    pwsvscaval.y
    @17
    eqid
    pwsvscaval.b
    pwsvscaval.r
    pwsvscaval.i
    pwsvscaval.x
    pwselbas
    feqmptd
    offval2
    eqtr4d
    3eqtrd
end

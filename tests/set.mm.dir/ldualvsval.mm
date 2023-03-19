include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "ldualvs.mm"
include "fveq1d.mm"
include "wcel.mm"
include "wceq.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf.mm"
include "wfn.mm"
include "lflf.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "wa.mm"
include "eqidd.mm"
include "ofc2.mm"
include "mpdan.mm"
include "eqtrd.mm"

theorem ldualvsval
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vk: setvar k
  assume ldualfvs.f: |- F = ( LFnl ` W )
  assume ldualfvs.v: |- V = ( Base ` W )
  assume ldualfvs.r: |- R = ( Scalar ` W )
  assume ldualfvs.k: |- K = ( Base ` R )
  assume ldualfvs.t: |- .X. = ( .r ` R )
  assume ldualfvs.d: |- D = ( LDual ` W )
  assume ldualfvs.s: |- .xb = ( .s ` D )
  assume ldualfvs.w: |- ( ph -> W e. Y )
  assume ldualvs.x: |- ( ph -> X e. K )
  assume ldualvs.g: |- ( ph -> G e. F )
  assume ldualvs.a: |- ( ph -> A e. V )


  assert |- ( ph -> ( ( X .xb G ) ` A ) = ( ( G ` A ) .X. X ) )

  proof
    wph
    cA
    cX
    cG
    c.xb
    co
    #
    cfv
    cA
    cG
    cV
    cX
    csn
    cxp
    c.xp
    cof
    co
    #
    cfv
    #
    cA
    cG
    cfv
    #
    cX
    c.xp
    co
    #
    wph
    cA
    @0
    @1
    wph
    cD
    cR
    c.xb
    c.xp
    cF
    cG
    cK
    cV
    cW
    cX
    cY
    ldualfvs.f
    ldualfvs.v
    ldualfvs.r
    ldualfvs.k
    ldualfvs.t
    ldualfvs.d
    ldualfvs.s
    ldualfvs.w
    ldualvs.x
    ldualvs.g
    ldualvs
    fveq1d
    wph
    cA
    cV
    wcel
    #
    @2
    @4
    wceq
    ldualvs.a
    wph
    cV
    cX
    @3
    c.xp
    cG
    cvv
    cK
    cA
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    ldualfvs.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    ldualvs.x
    wph
    cV
    cK
    cG
    wf
    #
    cG
    cV
    wfn
    wph
    cW
    cY
    wcel
    cG
    cF
    wcel
    @6
    ldualfvs.w
    ldualvs.g
    cR
    cF
    cG
    cK
    cV
    cW
    cY
    ldualfvs.r
    ldualfvs.k
    ldualfvs.v
    ldualfvs.f
    lflf
    syl2anc
    cV
    cK
    cG
    ffn
    syl
    wph
    @5
    wa
    @3
    eqidd
    ofc2
    mpdan
    eqtrd
end

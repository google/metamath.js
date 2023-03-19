include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ldualfvs.mm"
include "oveqd.mm"
include "wcel.mm"
include "wceq.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "oveq2d.mm"
include "oveq1.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem ldualvs
  let wph: wff ph
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


  assert |- ( ph -> ( X .xb G ) = ( G oF .X. ( V X. { X } ) ) )

  proof
    wph
    cX
    cG
    c.xb
    co
    cX
    cG
    vk
    vf
    cK
    cF
    vf
    cv
    #
    cV
    vk
    cv
    #
    csn
    #
    cxp
    #
    c.xp
    cof
    #
    co
    #
    cmpt2
    #
    co
    #
    cG
    cV
    cX
    csn
    #
    cxp
    #
    @4
    co
    #
    wph
    c.xb
    @6
    cX
    cG
    wph
    cD
    cR
    c.xb
    @6
    c.xp
    vf
    vk
    cF
    cK
    cV
    cW
    cY
    ldualfvs.f
    ldualfvs.v
    ldualfvs.r
    ldualfvs.k
    ldualfvs.t
    ldualfvs.d
    ldualfvs.s
    ldualfvs.w
    @6
    eqid
    #
    ldualfvs
    oveqd
    wph
    cX
    cK
    wcel
    cG
    cF
    wcel
    @7
    @10
    wceq
    ldualvs.x
    ldualvs.g
    vk
    vf
    cX
    cG
    cK
    cF
    @5
    @10
    @6
    @0
    @9
    @4
    co
    @1
    cX
    wceq
    #
    @3
    @9
    @0
    @4
    @12
    @2
    @8
    cV
    @1
    cX
    sneq
    xpeq2d
    oveq2d
    @0
    cG
    @9
    @4
    oveq1
    @11
    cG
    @9
    @4
    ovex
    ovmpt2
    syl2anc
    eqtrd
end

include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "clmod.mm"
include "wf.mm"
include "lflf.mm"
include "syl2anc.mm"
include "crg.mm"
include "lmodring.mm"
include "syl.mm"
include "ring0cl.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "ringrz.mm"
include "sylan.mm"
include "caofid1.mm"

theorem lfl0sc
  let wph: wff ph
  let cD: class D
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  assume lfl0sc.v: |- V = ( Base ` W )
  assume lfl0sc.d: |- D = ( Scalar ` W )
  assume lfl0sc.f: |- F = ( LFnl ` W )
  assume lfl0sc.k: |- K = ( Base ` D )
  assume lfl0sc.t: |- .x. = ( .r ` D )
  assume lfl0sc.o: |- .0. = ( 0g ` D )
  assume lfl0sc.w: |- ( ph -> W e. LMod )
  assume lfl0sc.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( G oF .x. ( V X. { .0. } ) ) = ( V X. { .0. } ) )

  proof
    wph
    vk
    cV
    c.0
    c.0
    c.x
    cK
    cG
    cvv
    cK
    cK
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lfl0sc.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    wph
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    cV
    cK
    cG
    wf
    lfl0sc.w
    lfl0sc.g
    cD
    cF
    cG
    cK
    cV
    cW
    clmod
    lfl0sc.d
    lfl0sc.k
    lfl0sc.v
    lfl0sc.f
    lflf
    syl2anc
    wph
    cD
    crg
    wcel
    #
    c.0
    cK
    wcel
    wph
    @0
    @1
    lfl0sc.w
    cD
    cW
    lfl0sc.d
    lmodring
    syl
    #
    cK
    cD
    c.0
    lfl0sc.k
    lfl0sc.o
    ring0cl
    syl
    #
    @3
    wph
    @1
    vk
    cv
    #
    cK
    wcel
    @4
    c.0
    c.x
    co
    c.0
    wceq
    @2
    cK
    cD
    c.x
    @4
    c.0
    lfl0sc.k
    lfl0sc.t
    lfl0sc.o
    ringrz
    sylan
    caofid1
end

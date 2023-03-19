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
include "cur.mm"
include "crg.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "lmodring.mm"
include "syl.mm"
include "ringridm.mm"
include "sylan.mm"
include "caofid0r.mm"

theorem lfl1sc
  let wph: wff ph
  let cD: class D
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let vk: setvar k
  assume lfl1sc.v: |- V = ( Base ` W )
  assume lfl1sc.d: |- D = ( Scalar ` W )
  assume lfl1sc.f: |- F = ( LFnl ` W )
  assume lfl1sc.k: |- K = ( Base ` D )
  assume lfl1sc.t: |- .x. = ( .r ` D )
  assume lfl1sc.i: |- .1. = ( 1r ` D )
  assume lfl1sc.w: |- ( ph -> W e. LMod )
  assume lfl1sc.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( G oF .x. ( V X. { .1. } ) ) = G )

  proof
    wph
    vk
    cV
    c.1
    c.x
    cK
    cG
    cvv
    cvv
    cV
    cvv
    wcel
    wph
    cV
    cW
    cbs
    cfv
    cvv
    lfl1sc.v
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
    lfl1sc.w
    lfl1sc.g
    cD
    cF
    cG
    cK
    cV
    cW
    clmod
    lfl1sc.d
    lfl1sc.k
    lfl1sc.v
    lfl1sc.f
    lflf
    syl2anc
    c.1
    cvv
    wcel
    wph
    c.1
    cD
    cur
    cfv
    cvv
    lfl1sc.i
    cD
    cur
    fvex
    eqeltri
    a1i
    wph
    cD
    crg
    wcel
    #
    vk
    cv
    #
    cK
    wcel
    @2
    c.1
    c.x
    co
    @2
    wceq
    wph
    @0
    @1
    lfl1sc.w
    cD
    cW
    lfl1sc.d
    lmodring
    syl
    cK
    cD
    c.x
    c.1
    @2
    lfl1sc.k
    lfl1sc.t
    lfl1sc.i
    ringridm
    sylan
    caofid0r
end

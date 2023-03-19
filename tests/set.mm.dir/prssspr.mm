include "cspr.mm"
include "cfv.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "ssel2.mm"
include "sprel.mm"
include "syl.mm"

theorem prssspr
  let cP: class P
  let cV: class V
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let cW: class W
  let vk: setvar k
  let vx: setvar x

  disjoint V a
  disjoint V b
  disjoint a b
  disjoint X a
  disjoint X b
  disjoint V p
  disjoint a p
  disjoint b p
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint X p
  disjoint k x
  assert |- ( ( P C_ ( Pairs ` V ) /\ X e. P ) -> E. a e. V E. b e. V X = { a , b } )

  proof
    cP
    cV
    cspr
    cfv
    #
    wss
    cX
    cP
    wcel
    wa
    cX
    @0
    wcel
    cX
    va
    cv
    vb
    cv
    cpr
    wceq
    vb
    cV
    wrex
    va
    cV
    wrex
    cP
    @0
    cX
    ssel2
    cV
    cX
    va
    vb
    sprel
    syl
end

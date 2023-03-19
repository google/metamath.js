include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "weu.mm"
include "hashen1.mm"
include "euen1b.mm"
include "syl6bb.mm"

theorem euhash1
  let cV: class V
  let cW: class W
  let va: setvar a

  disjoint V a
  assert |- ( V e. W -> ( ( # ` V ) = 1 <-> E! a a e. V ) )

  proof
    cV
    cW
    wcel
    cV
    chash
    cfv
    c1
    wceq
    cV
    c1o
    cen
    wbr
    va
    cv
    cV
    wcel
    va
    weu
    cV
    cW
    hashen1
    va
    cV
    euen1b
    syl6bb
end

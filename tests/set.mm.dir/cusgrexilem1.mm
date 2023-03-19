include "wcel.mm"
include "cvv.mm"
include "cid.mm"
include "cres.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "pwexg.mm"
include "rabexd.mm"
include "resiexg.mm"
include "syl.mm"

theorem cusgrexilem1
  let vx: setvar x
  let cP: class P
  let cV: class V
  let cW: class W
  assume usgrexi.p: |- P = { x e. ~P V | ( # ` x ) = 2 }

  disjoint V x
  assert |- ( V e. W -> ( _I |` P ) e. _V )

  proof
    cV
    cW
    wcel
    #
    cP
    cvv
    wcel
    cid
    cP
    cres
    cvv
    wcel
    @0
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cV
    cpw
    cP
    cvv
    usgrexi.p
    cV
    cW
    pwexg
    rabexd
    cP
    cvv
    resiexg
    syl
end

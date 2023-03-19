include "c2.mm"
include "co.mm"
include "cclwwlknon.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "oveqi.mm"
include "clwwlknon.mm"
include "eqtri.mm"

theorem clwwlknon2
  let vw: setvar w
  let cC: class C
  let cG: class G
  let cX: class X
  assume clwwlknon2.c: |- C = ( ClWWalksNOn ` G )

  disjoint G w
  disjoint X w
  assert |- ( X C 2 ) = { w e. ( 2 ClWWalksN G ) | ( w ` 0 ) = X }

  proof
    cX
    c2
    cC
    co
    cX
    c2
    cG
    cclwwlknon
    cfv
    #
    co
    cc0
    vw
    cv
    cfv
    cX
    wceq
    vw
    c2
    cG
    cclwwlkn
    co
    crab
    cC
    @0
    cX
    c2
    clwwlknon2.c
    oveqi
    vw
    cG
    c2
    cX
    clwwlknon
    eqtri
end

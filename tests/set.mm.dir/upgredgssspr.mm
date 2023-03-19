include "cupgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cspr.mm"
include "upgredgss.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "sprvalpwle2.mm"
include "ax-mp.mm"
include "syl6sseqr.mm"

theorem upgredgssspr
  let cG: class G
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x


  assert |- ( G e. UPGraph -> ( Edg ` G ) C_ ( Pairs ` ( Vtx ` G ) ) )

  proof
    cG
    cupgr
    wcel
    cG
    cedg
    cfv
    vp
    cv
    chash
    cfv
    c2
    cle
    wbr
    vp
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    crab
    #
    @0
    cspr
    cfv
    #
    vp
    cG
    upgredgss
    @0
    cvv
    wcel
    @2
    @1
    wceq
    cG
    cvtx
    fvex
    @0
    cvv
    vp
    sprvalpwle2
    ax-mp
    syl6sseqr
end

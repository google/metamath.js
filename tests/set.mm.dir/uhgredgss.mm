include "cuhgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "uhgredgn0.mm"
include "ex.mm"
include "ssrdv.mm"

theorem uhgredgss
  let cG: class G
  let vx: setvar x


  assert |- ( G e. UHGraph -> ( Edg ` G ) C_ ( ~P ( Vtx ` G ) \ { (/) } ) )

  proof
    cG
    cuhgr
    wcel
    #
    vx
    cG
    cedg
    cfv
    #
    cG
    cvtx
    cfv
    cpw
    c0
    csn
    cdif
    #
    @0
    vx
    cv
    #
    @1
    wcel
    @3
    @2
    wcel
    @3
    cG
    uhgredgn0
    ex
    ssrdv
end

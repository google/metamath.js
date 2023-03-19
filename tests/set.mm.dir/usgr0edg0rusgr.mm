include "cusgr.mm"
include "wcel.mm"
include "cc0.mm"
include "crusgr.mm"
include "wbr.mm"
include "crgr.mm"
include "wa.mm"
include "cedg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cn0.mm"
include "wb.mm"
include "0nn0.mm"
include "isrusgr.mm"
include "mpan2.mm"
include "ibar.mm"
include "cuhgr.mm"
include "usgruhgr.mm"
include "uhgr0edg0rgrb.mm"
include "syl.mm"
include "3bitr2d.mm"

theorem usgr0edg0rusgr
  let cG: class G
  let vv: setvar v
  let cW: class W


  assert |- ( G e. USGraph -> ( G RegUSGraph 0 <-> ( Edg ` G ) = (/) ) )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cc0
    crusgr
    wbr
    #
    @0
    cG
    cc0
    crgr
    wbr
    #
    wa
    #
    @2
    cG
    cedg
    cfv
    c0
    wceq
    #
    @0
    cc0
    cn0
    wcel
    @1
    @3
    wb
    0nn0
    cG
    cc0
    cusgr
    cn0
    isrusgr
    mpan2
    @0
    @2
    ibar
    @0
    cG
    cuhgr
    wcel
    @2
    @4
    wb
    cG
    usgruhgr
    cG
    uhgr0edg0rgrb
    syl
    3bitr2d
end

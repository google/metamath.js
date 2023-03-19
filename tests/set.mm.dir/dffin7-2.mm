include "cfin7.mm"
include "cfn.mm"
include "cvv.mm"
include "ccrd.mm"
include "cdm.mm"
include "cdif.mm"
include "cun.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "imor.mm"
include "wb.mm"
include "vex.mm"
include "isfin7-2.mm"
include "ax-mp.mm"
include "elun.mm"
include "orcom.mm"
include "eldif.mm"
include "mpbiran.mm"
include "orbi1i.mm"
include "3bitri.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem dffin7-2
  let vx: setvar x


  assert |- Fin7 = ( Fin u. ( _V \ dom card ) )

  proof
    vx
    cfin7
    cfn
    cvv
    ccrd
    cdm
    #
    cdif
    #
    cun
    #
    vx
    cv
    #
    @0
    wcel
    #
    @3
    cfn
    wcel
    #
    wi
    #
    @4
    wn
    #
    @5
    wo
    #
    @3
    cfin7
    wcel
    #
    @3
    @2
    wcel
    #
    @4
    @5
    imor
    @3
    cvv
    wcel
    #
    @9
    @6
    wb
    vx
    vex
    #
    @3
    cvv
    isfin7-2
    ax-mp
    @10
    @5
    @3
    @1
    wcel
    #
    wo
    @13
    @5
    wo
    @8
    @3
    cfn
    @1
    elun
    @5
    @13
    orcom
    @13
    @7
    @5
    @13
    @11
    @7
    @12
    @3
    cvv
    @0
    eldif
    mpbiran
    orbi1i
    3bitri
    3bitr4i
    eqriv
end

include "wcel.mm"
include "cvv.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "clsw.mm"
include "wceq.mm"
include "elex.mm"
include "fvex.mm"
include "cv.mm"
include "id.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq12d.mm"
include "df-lsw.mm"
include "fvmptg.mm"
include "sylancl.mm"

theorem lsw
  let cW: class W
  let cX: class X
  let vw: setvar w


  assert |- ( W e. X -> ( lastS ` W ) = ( W ` ( ( # ` W ) - 1 ) ) )

  proof
    cW
    cX
    wcel
    cW
    cvv
    wcel
    cW
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cW
    cfv
    #
    cvv
    wcel
    cW
    clsw
    cfv
    @2
    wceq
    cW
    cX
    elex
    @1
    cW
    fvex
    vw
    cW
    vw
    cv
    #
    chash
    cfv
    #
    c1
    cmin
    co
    #
    @3
    cfv
    @2
    cvv
    cvv
    clsw
    @3
    cW
    wceq
    #
    @5
    @1
    @3
    cW
    @6
    id
    @6
    @4
    @0
    c1
    cmin
    @3
    cW
    chash
    fveq2
    oveq1d
    fveq12d
    vw
    df-lsw
    fvmptg
    sylancl
end

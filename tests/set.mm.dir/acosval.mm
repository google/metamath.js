include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "casin.mm"
include "cfv.mm"
include "cmin.mm"
include "cc.mm"
include "cacos.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "df-acos.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem acosval
  let cA: class A
  let vx: setvar x


  assert |- ( A e. CC -> ( arccos ` A ) = ( ( _pi / 2 ) - ( arcsin ` A ) ) )

  proof
    vx
    cA
    cpi
    c2
    cdiv
    co
    #
    vx
    cv
    #
    casin
    cfv
    #
    cmin
    co
    @0
    cA
    casin
    cfv
    #
    cmin
    co
    cc
    cacos
    @1
    cA
    wceq
    @2
    @3
    @0
    cmin
    @1
    cA
    casin
    fveq2
    oveq2d
    vx
    df-acos
    @0
    @3
    cmin
    ovex
    fvmpt
end

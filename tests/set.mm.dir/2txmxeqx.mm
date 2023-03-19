include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "2times.mm"
include "oveq1d.mm"
include "id.mm"
include "pncan2d.mm"
include "eqtrd.mm"

theorem 2txmxeqx
  let cX: class X


  assert |- ( X e. CC -> ( ( 2 x. X ) - X ) = X )

  proof
    cX
    cc
    wcel
    #
    c2
    cX
    cmul
    co
    #
    cX
    cmin
    co
    cX
    cX
    caddc
    co
    #
    cX
    cmin
    co
    cX
    @0
    @1
    @2
    cX
    cmin
    cX
    2times
    oveq1d
    @0
    cX
    cX
    @0
    id
    #
    @3
    pncan2d
    eqtrd
end

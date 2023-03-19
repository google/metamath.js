include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "caddc.mm"
include "ccos.mm"
include "2times.mm"
include "fveq2d.mm"
include "coscl.mm"
include "sincl.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "sinadd.mm"
include "anidms.mm"
include "mulcld.mm"
include "2timesd.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"

theorem sin2t
  let cA: class A


  assert |- ( A e. CC -> ( sin ` ( 2 x. A ) ) = ( 2 x. ( ( sin ` A ) x. ( cos ` A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    c2
    cA
    cmul
    co
    #
    csin
    cfv
    cA
    cA
    caddc
    co
    #
    csin
    cfv
    #
    c2
    cA
    csin
    cfv
    #
    cA
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    @0
    @1
    @2
    csin
    cA
    2times
    fveq2d
    @0
    @6
    @5
    @4
    cmul
    co
    #
    caddc
    co
    #
    @6
    @6
    caddc
    co
    @3
    @7
    @0
    @8
    @6
    @6
    caddc
    @0
    @5
    @4
    cA
    coscl
    #
    cA
    sincl
    #
    mulcomd
    oveq2d
    @0
    @3
    @9
    wceq
    cA
    cA
    sinadd
    anidms
    @0
    @6
    @0
    @4
    @5
    @11
    @10
    mulcld
    2timesd
    3eqtr4d
    eqtrd
end

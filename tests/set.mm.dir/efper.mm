include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ce.mm"
include "cfv.mm"
include "wceq.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "zcn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efadd.mm"
include "sylan2.mm"
include "c1.mm"
include "ef2kpi.mm"
include "oveq2d.mm"
include "efcl.mm"
include "mulid1d.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"

theorem efper
  let cA: class A
  let cK: class K


  assert |- ( ( A e. CC /\ K e. ZZ ) -> ( exp ` ( A + ( ( _i x. ( 2 x. _pi ) ) x. K ) ) ) = ( exp ` A ) )

  proof
    cA
    cc
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    cA
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cK
    cmul
    co
    #
    caddc
    co
    ce
    cfv
    #
    cA
    ce
    cfv
    #
    @4
    ce
    cfv
    #
    cmul
    co
    #
    @6
    @1
    @0
    @4
    cc
    wcel
    #
    @5
    @8
    wceq
    @1
    @3
    cc
    wcel
    cK
    cc
    wcel
    @9
    ci
    @2
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    mulcli
    cK
    zcn
    @3
    cK
    mulcl
    sylancr
    cA
    @4
    efadd
    sylan2
    @1
    @0
    @8
    @6
    c1
    cmul
    co
    @6
    @1
    @7
    c1
    @6
    cmul
    cK
    ef2kpi
    oveq2d
    @0
    @6
    cA
    efcl
    mulid1d
    sylan9eqr
    eqtrd
end

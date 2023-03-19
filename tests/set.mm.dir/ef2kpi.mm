include "cz.mm"
include "wcel.mm"
include "ci.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cexp.mm"
include "c1.mm"
include "cc.mm"
include "wceq.mm"
include "ax-icn.mm"
include "2cn.mm"
include "picn.mm"
include "mulcli.mm"
include "zcn.mm"
include "mulcom.mm"
include "sylancr.mm"
include "fveq2d.mm"
include "efexp.mm"
include "mpan.mm"
include "ef2pi.mm"
include "oveq1i.mm"
include "1exp.mm"
include "syl5eq.mm"
include "3eqtrd.mm"

theorem ef2kpi
  let cK: class K


  assert |- ( K e. ZZ -> ( exp ` ( ( _i x. ( 2 x. _pi ) ) x. K ) ) = 1 )

  proof
    cK
    cz
    wcel
    #
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
    ce
    cfv
    cK
    @2
    cmul
    co
    #
    ce
    cfv
    #
    @2
    ce
    cfv
    #
    cK
    cexp
    co
    #
    c1
    @0
    @3
    @4
    ce
    @0
    @2
    cc
    wcel
    #
    cK
    cc
    wcel
    @3
    @4
    wceq
    ci
    @1
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    mulcli
    #
    cK
    zcn
    @2
    cK
    mulcom
    sylancr
    fveq2d
    @8
    @0
    @5
    @7
    wceq
    @9
    @2
    cK
    efexp
    mpan
    @0
    @7
    c1
    cK
    cexp
    co
    c1
    @6
    c1
    cK
    cexp
    ef2pi
    oveq1i
    cK
    1exp
    syl5eq
    3eqtrd
end

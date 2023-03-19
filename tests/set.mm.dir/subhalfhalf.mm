include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "id.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divcan1d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "halfcl.mm"
include "mulcomd.mm"
include "c1.mm"
include "mulsubfacd.mm"
include "wceq.mm"
include "2m1e1.mm"
include "mulid2d.mm"
include "3eqtrd.mm"

theorem subhalfhalf
  let cA: class A


  assert |- ( A e. CC -> ( A - ( A / 2 ) ) = ( A / 2 ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cA
    c2
    cdiv
    co
    #
    cmin
    co
    @1
    c2
    cmul
    co
    #
    @1
    cmin
    co
    c2
    @1
    cmul
    co
    #
    @1
    cmin
    co
    #
    @1
    @0
    cA
    @2
    @1
    cmin
    @0
    @2
    cA
    @0
    cA
    c2
    @0
    id
    @0
    2cnd
    #
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    divcan1d
    eqcomd
    oveq1d
    @0
    @2
    @3
    @1
    cmin
    @0
    @1
    c2
    cA
    halfcl
    #
    @5
    mulcomd
    oveq1d
    @0
    @4
    c2
    c1
    cmin
    co
    #
    @1
    cmul
    co
    c1
    @1
    cmul
    co
    @1
    @0
    c2
    @1
    @5
    @6
    mulsubfacd
    @0
    @7
    c1
    @1
    cmul
    @7
    c1
    wceq
    @0
    2m1e1
    a1i
    oveq1d
    @0
    @1
    @6
    mulid2d
    3eqtrd
    3eqtrd
end

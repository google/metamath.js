include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "caddc.mm"
include "c1.mm"
include "cn0.mm"
include "uznn0sub.mm"
include "expcl.mm"
include "sylan2.mm"
include "3adant2.mm"
include "simp2.mm"
include "mulcl.mm"
include "3adant3.mm"
include "subadd23d.mm"
include "subcld.mm"
include "addcomd.mm"
include "simp1.mm"
include "mulsubfacd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem numclwlk3lem3
  let cK: class K
  let cN: class N
  let cY: class Y


  assert |- ( ( K e. CC /\ Y e. CC /\ N e. ( ZZ>= ` 2 ) ) -> ( ( ( K ^ ( N - 2 ) ) - Y ) + ( K x. Y ) ) = ( ( ( K - 1 ) x. Y ) + ( K ^ ( N - 2 ) ) ) )

  proof
    cK
    cc
    wcel
    #
    cY
    cc
    wcel
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    w3a
    #
    cK
    cN
    c2
    cmin
    co
    #
    cexp
    co
    #
    cY
    cmin
    co
    cK
    cY
    cmul
    co
    #
    caddc
    co
    @5
    @6
    cY
    cmin
    co
    #
    caddc
    co
    @7
    @5
    caddc
    co
    cK
    c1
    cmin
    co
    cY
    cmul
    co
    #
    @5
    caddc
    co
    @3
    @5
    cY
    @6
    @0
    @2
    @5
    cc
    wcel
    #
    @1
    @2
    @0
    @4
    cn0
    wcel
    @9
    c2
    cN
    uznn0sub
    cK
    @4
    expcl
    sylan2
    3adant2
    #
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @6
    cc
    wcel
    @2
    cK
    cY
    mulcl
    3adant3
    #
    subadd23d
    @3
    @5
    @7
    @10
    @3
    @6
    cY
    @12
    @11
    subcld
    addcomd
    @3
    @7
    @8
    @5
    caddc
    @3
    cK
    cY
    @0
    @1
    @2
    simp1
    @11
    mulsubfacd
    oveq1d
    3eqtrd
end

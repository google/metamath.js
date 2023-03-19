include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "cmpt.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "oveq2.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "oveq12d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"

theorem etransclem5
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cX: class X

  disjoint M j
  disjoint M k
  disjoint j k
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint k x
  assert |- ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) ) = ( k e. ( 0 ... M ) |-> ( y e. X |-> ( ( y - k ) ^ if ( k = 0 , ( P - 1 ) , P ) ) ) )

  proof
    vj
    vk
    cc0
    cM
    cfz
    co
    vx
    cX
    vx
    cv
    #
    vj
    cv
    #
    cmin
    co
    #
    @1
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    vy
    cX
    vy
    cv
    #
    vk
    cv
    #
    cmin
    co
    #
    @9
    cc0
    wceq
    #
    @4
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    @1
    @9
    wceq
    #
    @7
    vy
    cX
    @8
    @1
    cmin
    co
    #
    @5
    cexp
    co
    #
    cmpt
    @14
    vx
    vy
    cX
    @6
    @17
    @0
    @8
    wceq
    @2
    @16
    @5
    cexp
    @0
    @8
    @1
    cmin
    oveq1
    oveq1d
    cbvmptv
    @15
    vy
    cX
    @17
    @13
    @15
    @16
    @10
    @5
    @12
    cexp
    @1
    @9
    @8
    cmin
    oveq2
    @15
    @3
    @11
    @4
    cP
    @1
    @9
    cc0
    eqeq1
    ifbid
    oveq12d
    mpteq2dv
    syl5eq
    cbvmptv
end

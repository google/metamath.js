include "cr.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cfz.mm"
include "cprod.mm"
include "cmul.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvprodv.mm"
include "prodeq2ad.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "cbvmptv.mm"

theorem etransclem6
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cM: class M

  disjoint M j
  disjoint M k
  disjoint M x
  disjoint M y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint k x
  assert |- ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) ) = ( y e. RR |-> ( ( y ^ ( P - 1 ) ) x. prod_ k e. ( 1 ... M ) ( ( y - k ) ^ P ) ) )

  proof
    vx
    vy
    cr
    vx
    cv
    #
    cP
    c1
    cmin
    co
    #
    cexp
    co
    #
    c1
    cM
    cfz
    co
    #
    @0
    vj
    cv
    #
    cmin
    co
    #
    cP
    cexp
    co
    #
    vj
    cprod
    #
    cmul
    co
    vy
    cv
    #
    @1
    cexp
    co
    #
    @3
    @8
    vk
    cv
    #
    cmin
    co
    #
    cP
    cexp
    co
    #
    vk
    cprod
    #
    cmul
    co
    vx
    vy
    weq
    #
    @2
    @9
    @7
    @13
    cmul
    @0
    @8
    @1
    cexp
    oveq1
    @14
    @7
    @3
    @0
    @10
    cmin
    co
    #
    cP
    cexp
    co
    #
    vk
    cprod
    @13
    @3
    @6
    @16
    vj
    vk
    vj
    vk
    weq
    @5
    @15
    cP
    cexp
    @4
    @10
    @0
    cmin
    oveq2
    oveq1d
    cbvprodv
    @14
    @3
    @16
    @12
    vk
    @14
    @15
    @11
    cP
    cexp
    @0
    @8
    @10
    cmin
    oveq1
    oveq1d
    prodeq2ad
    syl5eq
    oveq12d
    cbvmptv
end

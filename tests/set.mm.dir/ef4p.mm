include "cc.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c3.mm"
include "c6.mm"
include "c4.mm"
include "df-4.mm"
include "3nn0.mm"
include "id.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "mpan.mm"
include "sqcl.mm"
include "halfcld.mm"
include "addcld.mm"
include "df-3.mm"
include "2nn0.mm"
include "df-2.mm"
include "1nn0.mm"
include "a1i.mm"
include "cc0.mm"
include "1e0p1.mm"
include "0nn0.mm"
include "0cnd.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "ce.mm"
include "cn0.mm"
include "efval2.mm"
include "nn0uz.mm"
include "sumeq1i.mm"
include "syl6req.mm"
include "oveq2d.mm"
include "efcl.mm"
include "addid2d.mm"
include "eqtr2d.mm"
include "cfa.mm"
include "eft0val.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "efsep.mm"
include "exp1.mm"
include "wceq.mm"
include "fac1.mm"
include "oveq12d.mm"
include "div1.mm"
include "eqtrd.mm"
include "fac2.mm"
include "oveq2i.mm"
include "fac3.mm"

theorem ef4p
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  assume ef4p.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  assert |- ( A e. CC -> ( exp ` A ) = ( ( ( ( 1 + A ) + ( ( A ^ 2 ) / 2 ) ) + ( ( A ^ 3 ) / 6 ) ) + sum_ k e. ( ZZ>= ` 4 ) ( F ` k ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    c1
    cA
    caddc
    co
    #
    cA
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @4
    cA
    c3
    cexp
    co
    #
    c6
    cdiv
    co
    #
    caddc
    co
    #
    vk
    vn
    cF
    c3
    c4
    ef4p.1
    df-4
    3nn0
    @0
    id
    #
    @0
    @1
    @3
    c1
    cc
    wcel
    #
    @0
    @1
    cc
    wcel
    ax-1cn
    c1
    cA
    addcl
    mpan
    #
    @0
    @2
    cA
    sqcl
    halfcld
    addcld
    @0
    cA
    @1
    @4
    vk
    vn
    cF
    c2
    c3
    ef4p.1
    df-3
    2nn0
    @8
    @10
    @0
    cA
    c1
    @1
    vk
    vn
    cF
    c1
    c2
    ef4p.1
    df-2
    1nn0
    @8
    @9
    @0
    ax-1cn
    a1i
    @0
    cA
    cc0
    c1
    vk
    vn
    cF
    cc0
    c1
    ef4p.1
    1e0p1
    0nn0
    @8
    @0
    0cnd
    @0
    cc0
    cc0
    cuz
    cfv
    #
    vk
    cv
    cF
    cfv
    #
    vk
    csu
    #
    caddc
    co
    cc0
    cA
    ce
    cfv
    #
    caddc
    co
    @14
    @0
    @13
    @14
    cc0
    caddc
    @0
    @14
    cn0
    @12
    vk
    csu
    @13
    cA
    vk
    vn
    cF
    ef4p.1
    efval2
    cn0
    @11
    @12
    vk
    nn0uz
    sumeq1i
    syl6req
    oveq2d
    @0
    @14
    cA
    efcl
    addid2d
    eqtr2d
    @0
    cc0
    cA
    cc0
    cexp
    co
    cc0
    cfa
    cfv
    cdiv
    co
    #
    caddc
    co
    cc0
    c1
    caddc
    co
    c1
    @0
    @15
    c1
    cc0
    caddc
    cA
    eft0val
    oveq2d
    0p1e1
    syl6eq
    efsep
    @0
    cA
    c1
    cexp
    co
    #
    c1
    cfa
    cfv
    #
    cdiv
    co
    #
    cA
    c1
    caddc
    @0
    @18
    cA
    c1
    cdiv
    co
    cA
    @0
    @16
    cA
    @17
    c1
    cdiv
    cA
    exp1
    @17
    c1
    wceq
    @0
    fac1
    a1i
    oveq12d
    cA
    div1
    eqtrd
    oveq2d
    efsep
    @1
    @2
    c2
    cfa
    cfv
    #
    cdiv
    co
    #
    caddc
    co
    @4
    wceq
    @0
    @20
    @3
    @1
    caddc
    @19
    c2
    @2
    cdiv
    fac2
    oveq2i
    oveq2i
    a1i
    efsep
    @4
    @5
    c3
    cfa
    cfv
    #
    cdiv
    co
    #
    caddc
    co
    @7
    wceq
    @0
    @22
    @6
    @4
    caddc
    @21
    c6
    @5
    cdiv
    fac3
    oveq2i
    oveq2i
    a1i
    efsep
end

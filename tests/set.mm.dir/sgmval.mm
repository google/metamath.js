include "cc.mm"
include "cn.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "ccxp.mm"
include "co.mm"
include "csu.mm"
include "csgm.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "wcel.mm"
include "simpll.mm"
include "oveq2d.mm"
include "sumeq12dv.mm"
include "df-sgm.mm"
include "sumex.mm"
include "ovmpt2a.mm"

theorem sgmval
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vp: setvar p
  let vn: setvar n
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cP: class P

  disjoint k p
  disjoint A k
  disjoint A p
  disjoint B k
  disjoint B p
  disjoint k n
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint K p
  disjoint M p
  disjoint M x
  disjoint N p
  disjoint S s
  disjoint S x
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P p
  assert |- ( ( A e. CC /\ B e. NN ) -> ( A sigma B ) = sum_ k e. { p e. NN | p || B } ( k ^c A ) )

  proof
    vx
    vn
    cA
    cB
    cc
    cn
    vp
    cv
    #
    vn
    cv
    #
    cdvds
    wbr
    #
    vp
    cn
    crab
    #
    vk
    cv
    #
    vx
    cv
    #
    ccxp
    co
    #
    vk
    csu
    @0
    cB
    cdvds
    wbr
    #
    vp
    cn
    crab
    #
    @4
    cA
    ccxp
    co
    #
    vk
    csu
    csgm
    @5
    cA
    wceq
    #
    @1
    cB
    wceq
    #
    wa
    #
    @3
    @8
    @6
    @9
    vk
    @12
    @2
    @7
    vp
    cn
    @12
    @1
    cB
    @0
    cdvds
    @10
    @11
    simpr
    breq2d
    rabbidv
    @12
    @4
    @3
    wcel
    #
    wa
    @5
    cA
    @4
    ccxp
    @10
    @11
    @13
    simpll
    oveq2d
    sumeq12dv
    vx
    vk
    vn
    vp
    df-sgm
    @8
    @9
    vk
    sumex
    ovmpt2a
end

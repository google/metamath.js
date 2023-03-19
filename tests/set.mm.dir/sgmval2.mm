include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "csgm.mm"
include "co.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "ccxp.mm"
include "csu.mm"
include "cexp.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "sgmval.mm"
include "sylan.mm"
include "ssrab2.mm"
include "simpr.mm"
include "sseldi.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "simpll.mm"
include "cxpexpzd.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"

theorem sgmval2
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
  assert |- ( ( A e. ZZ /\ B e. NN ) -> ( A sigma B ) = sum_ k e. { p e. NN | p || B } ( k ^ A ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    csgm
    co
    #
    vp
    cv
    cB
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
    cA
    ccxp
    co
    #
    vk
    csu
    #
    @5
    @6
    cA
    cexp
    co
    #
    vk
    csu
    @0
    cA
    cc
    wcel
    @1
    @3
    @8
    wceq
    cA
    zcn
    cA
    cB
    vk
    vp
    sgmval
    sylan
    @2
    @5
    @7
    @9
    vk
    @2
    @6
    @5
    wcel
    #
    wa
    #
    @6
    cA
    @11
    @6
    @11
    @5
    cn
    @6
    @4
    vp
    cn
    ssrab2
    @2
    @10
    simpr
    sseldi
    #
    nncnd
    @11
    @6
    @12
    nnne0d
    @0
    @1
    @10
    simpll
    cxpexpzd
    sumeq2dv
    eqtrd
end

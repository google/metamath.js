include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "wrex.mm"
include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "cif.mm"
include "cn.mm"
include "cmu.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "ifbieq2d.mm"
include "df-mu.mm"
include "c0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem muval
  let cA: class A
  let vp: setvar p
  let vk: setvar k
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
  let cB: class B
  let cP: class P

  disjoint A p
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
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
  disjoint B k
  disjoint B n
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P p
  assert |- ( A e. NN -> ( mmu ` A ) = if ( E. p e. Prime ( p ^ 2 ) || A , 0 , ( -u 1 ^ ( # ` { p e. Prime | p || A } ) ) ) )

  proof
    vx
    cA
    vp
    cv
    #
    c2
    cexp
    co
    #
    vx
    cv
    #
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    cc0
    c1
    cneg
    #
    @0
    @2
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    cexp
    co
    #
    cif
    @1
    cA
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    cc0
    @5
    @0
    cA
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    cexp
    co
    #
    cif
    cn
    cmu
    @2
    cA
    wceq
    #
    @4
    @11
    @9
    @15
    cc0
    @16
    @3
    @10
    vp
    cprime
    @2
    cA
    @1
    cdvds
    breq2
    rexbidv
    @16
    @8
    @14
    @5
    cexp
    @16
    @7
    @13
    chash
    @16
    @6
    @12
    vp
    cprime
    @2
    cA
    @0
    cdvds
    breq2
    rabbidv
    fveq2d
    oveq2d
    ifbieq2d
    vx
    vp
    df-mu
    @11
    cc0
    @15
    c0ex
    @5
    @14
    cexp
    ovex
    ifex
    fvmpt
end

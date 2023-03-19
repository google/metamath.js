include "cn.mm"
include "wcel.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cneg.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "chash.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "wn.mm"
include "df-ne.mm"
include "wo.mm"
include "c2.mm"
include "wrex.mm"
include "cif.mm"
include "ifeqor.mm"
include "muval.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "mpbiri.mm"
include "ord.mm"
include "syl5bi.mm"
include "imp.mm"

theorem muval2
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
  assert |- ( ( A e. NN /\ ( mmu ` A ) =/= 0 ) -> ( mmu ` A ) = ( -u 1 ^ ( # ` { p e. Prime | p || A } ) ) )

  proof
    cA
    cn
    wcel
    #
    cA
    cmu
    cfv
    #
    cc0
    wne
    #
    @1
    c1
    cneg
    vp
    cv
    #
    cA
    cdvds
    wbr
    vp
    cprime
    crab
    chash
    cfv
    cexp
    co
    #
    wceq
    #
    @2
    @1
    cc0
    wceq
    #
    wn
    @0
    @5
    @1
    cc0
    df-ne
    @0
    @6
    @5
    @0
    @6
    @5
    wo
    @3
    c2
    cexp
    co
    cA
    cdvds
    wbr
    vp
    cprime
    wrex
    #
    cc0
    @4
    cif
    #
    cc0
    wceq
    #
    @8
    @4
    wceq
    #
    wo
    @7
    cc0
    @4
    ifeqor
    @0
    @6
    @9
    @5
    @10
    @0
    @1
    @8
    cc0
    cA
    vp
    muval
    #
    eqeq1d
    @0
    @1
    @8
    @4
    @11
    eqeq1d
    orbi12d
    mpbiri
    ord
    syl5bi
    imp
end

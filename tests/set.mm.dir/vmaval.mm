include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprime.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cuni.mm"
include "clog.mm"
include "cc0.mm"
include "cif.mm"
include "csb.mm"
include "cn.mm"
include "cvma.mm"
include "cvv.mm"
include "wcel.mm"
include "nnex.mm"
include "prmnn.mm"
include "ssriv.mm"
include "ssexi.mm"
include "rabex.mm"
include "a1i.mm"
include "wa.mm"
include "id.mm"
include "breq2.mm"
include "rabbidv.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "unieqd.mm"
include "ifbieq1d.mm"
include "csbied.mm"
include "df-vma.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem vmaval
  let cA: class A
  let cS: class S
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
  let cB: class B
  let cP: class P
  assume vmaval.1: |- S = { p e. Prime | p || A }

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
  assert |- ( A e. NN -> ( Lam ` A ) = if ( ( # ` S ) = 1 , ( log ` U. S ) , 0 ) )

  proof
    vx
    cA
    vs
    vp
    cv
    #
    vx
    cv
    #
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    vs
    cv
    #
    chash
    cfv
    #
    c1
    wceq
    #
    @4
    cuni
    #
    clog
    cfv
    #
    cc0
    cif
    #
    csb
    cS
    chash
    cfv
    #
    c1
    wceq
    #
    cS
    cuni
    #
    clog
    cfv
    #
    cc0
    cif
    #
    cn
    cvma
    @1
    cA
    wceq
    #
    vs
    @3
    @9
    @14
    cvv
    @3
    cvv
    wcel
    @15
    @2
    vp
    cprime
    cprime
    cn
    nnex
    vp
    cprime
    cn
    @0
    prmnn
    ssriv
    ssexi
    rabex
    a1i
    @15
    @4
    @3
    wceq
    #
    wa
    #
    @6
    @11
    @8
    @13
    cc0
    @17
    @5
    @10
    c1
    @17
    @4
    cS
    chash
    @16
    @15
    @4
    @3
    cS
    @16
    id
    @15
    @3
    @0
    cA
    cdvds
    wbr
    #
    vp
    cprime
    crab
    cS
    @15
    @2
    @18
    vp
    cprime
    @1
    cA
    @0
    cdvds
    breq2
    rabbidv
    vmaval.1
    syl6eqr
    sylan9eqr
    #
    fveq2d
    eqeq1d
    @17
    @7
    @12
    clog
    @17
    @4
    cS
    @19
    unieqd
    fveq2d
    ifbieq1d
    csbied
    vx
    vs
    vp
    df-vma
    @11
    @13
    cc0
    @12
    clog
    fvex
    c0ex
    ifex
    fvmpt
end

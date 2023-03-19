include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmo.mm"
include "cfl.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "crab.mm"
include "chash.mm"
include "cdiv.mm"
include "cmpt.mm"
include "cli.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "wral.mm"
include "c2.mm"
include "cuz.mm"
include "cr.mm"
include "snmlval.mm"
include "simp3bi.mm"
include "eqeq2.mm"
include "rabbidv.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "breq1d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem snmlflim
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let vr: setvar r
  let vb: setvar b
  assume snml.s: |- S = ( r e. ( ZZ>= ` 2 ) |-> { x e. RR | A. b e. ( 0 ... ( r - 1 ) ) ( n e. NN |-> ( ( # ` { k e. ( 1 ... n ) | ( |_ ` ( ( x x. ( r ^ k ) ) mod r ) ) = b } ) / n ) ) ~~> ( 1 / r ) } )
  assume snml.f: |- F = ( n e. NN |-> ( ( # ` { k e. ( 1 ... n ) | ( |_ ` ( ( A x. ( R ^ k ) ) mod R ) ) = B } ) / n ) )

  disjoint b k
  disjoint b n
  disjoint b x
  disjoint A b
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint B b
  disjoint B k
  disjoint B n
  disjoint F b
  disjoint b r
  disjoint R b
  disjoint k r
  disjoint R k
  disjoint n r
  disjoint R n
  disjoint r x
  disjoint R r
  disjoint R x
  assert |- ( ( A e. ( S ` R ) /\ B e. ( 0 ... ( R - 1 ) ) ) -> F ~~> ( 1 / R ) )

  proof
    cA
    cR
    cS
    cfv
    wcel
    #
    vn
    cn
    cA
    cR
    vk
    cv
    cexp
    co
    cmul
    co
    cR
    cmo
    co
    cfl
    cfv
    #
    vb
    cv
    #
    wceq
    #
    vk
    c1
    vn
    cv
    #
    cfz
    co
    #
    crab
    #
    chash
    cfv
    #
    @4
    cdiv
    co
    #
    cmpt
    #
    c1
    cR
    cdiv
    co
    #
    cli
    wbr
    #
    vb
    cc0
    cR
    c1
    cmin
    co
    cfz
    co
    #
    wral
    #
    cB
    @12
    wcel
    cF
    @10
    cli
    wbr
    #
    @0
    cR
    c2
    cuz
    cfv
    wcel
    cA
    cr
    wcel
    @13
    vx
    cA
    cR
    cS
    vk
    vn
    vr
    vb
    snml.s
    snmlval
    simp3bi
    @11
    @14
    vb
    cB
    @12
    @2
    cB
    wceq
    #
    @9
    cF
    @10
    cli
    @15
    @9
    vn
    cn
    @1
    cB
    wceq
    #
    vk
    @5
    crab
    #
    chash
    cfv
    #
    @4
    cdiv
    co
    #
    cmpt
    cF
    @15
    vn
    cn
    @8
    @19
    @15
    @7
    @18
    @4
    cdiv
    @15
    @6
    @17
    chash
    @15
    @3
    @16
    vk
    @5
    @2
    cB
    @1
    eqeq2
    rabbidv
    fveq2d
    oveq1d
    mpteq2dv
    snml.f
    syl6eqr
    breq1d
    rspccva
    sylan
end

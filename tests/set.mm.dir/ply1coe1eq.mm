include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cn0.mm"
include "wral.mm"
include "eqcoe1ply1eq.mm"
include "wa.mm"
include "cco1.mm"
include "fveq2.mm"
include "adantl.mm"
include "3eqtr4g.mm"
include "adantr.mm"
include "fveq1d.mm"
include "ralrimiva.mm"
include "ex.mm"
include "impbid.mm"

theorem ply1coe1eq
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cK: class K
  let cL: class L
  let vn: setvar n
  assume eqcoe1ply1eq.p: |- P = ( Poly1 ` R )
  assume eqcoe1ply1eq.b: |- B = ( Base ` P )
  assume eqcoe1ply1eq.a: |- A = ( coe1 ` K )
  assume eqcoe1ply1eq.c: |- C = ( coe1 ` L )

  disjoint A k
  disjoint C k
  disjoint B k
  disjoint K k
  disjoint L k
  disjoint R k
  disjoint A n
  disjoint k n
  disjoint B n
  disjoint C n
  disjoint K n
  disjoint L n
  disjoint P n
  disjoint R n
  assert |- ( ( R e. Ring /\ K e. B /\ L e. B ) -> ( A. k e. NN0 ( A ` k ) = ( C ` k ) <-> K = L ) )

  proof
    cR
    crg
    wcel
    cK
    cB
    wcel
    cL
    cB
    wcel
    w3a
    #
    vk
    cv
    #
    cA
    cfv
    @1
    cC
    cfv
    wceq
    #
    vk
    cn0
    wral
    #
    cK
    cL
    wceq
    #
    cA
    cB
    cC
    cP
    cR
    vk
    cK
    cL
    eqcoe1ply1eq.p
    eqcoe1ply1eq.b
    eqcoe1ply1eq.a
    eqcoe1ply1eq.c
    eqcoe1ply1eq
    @0
    @4
    @3
    @0
    @4
    wa
    #
    @2
    vk
    cn0
    @5
    @1
    cn0
    wcel
    #
    wa
    @1
    cA
    cC
    @5
    cA
    cC
    wceq
    @6
    @5
    cK
    cco1
    cfv
    #
    cL
    cco1
    cfv
    #
    cA
    cC
    @4
    @7
    @8
    wceq
    @0
    cK
    cL
    cco1
    fveq2
    adantl
    eqcoe1ply1eq.a
    eqcoe1ply1eq.c
    3eqtr4g
    adantr
    fveq1d
    ralrimiva
    ex
    impbid
end

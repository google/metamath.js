include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "wer.mm"
include "3ad2ant1.mm"
include "cvv.mm"
include "simp2l.mm"
include "ercpbllem.mm"
include "simp2r.mm"
include "anbi12d.mm"
include "wi.mm"
include "sylbid.mm"

theorem erlecpbl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.sm: class .~
  let cF: class F
  let cN: class N
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let c.pl: class .+
  assume ercpbl.r: |- ( ph -> .~ Er V )
  assume ercpbl.v: |- ( ph -> V e. _V )
  assume ercpbl.f: |- F = ( x e. V |-> [ x ] .~ )
  assume erlecpbl.e: |- ( ph -> ( ( A .~ C /\ B .~ D ) -> ( A N B <-> C N D ) ) )

  disjoint .~ x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint V x
  disjoint ph x
  disjoint a b
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint B b
  disjoint V a
  disjoint V b
  disjoint .+ a
  disjoint .+ b
  disjoint .+ x
  disjoint a ph
  disjoint b ph
  assert |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) -> ( A N B <-> C N D ) ) )

  proof
    wph
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    cD
    cV
    wcel
    wa
    #
    w3a
    #
    cA
    cF
    cfv
    cC
    cF
    cfv
    wceq
    #
    cB
    cF
    cfv
    cD
    cF
    cfv
    wceq
    #
    wa
    cA
    cC
    c.sm
    wbr
    #
    cB
    cD
    c.sm
    wbr
    #
    wa
    #
    cA
    cB
    cN
    wbr
    cC
    cD
    cN
    wbr
    wb
    #
    @4
    @5
    @7
    @6
    @8
    @4
    vx
    cA
    cC
    c.sm
    cF
    cV
    wph
    @2
    cV
    c.sm
    wer
    @3
    ercpbl.r
    3ad2ant1
    #
    wph
    @2
    cV
    cvv
    wcel
    @3
    ercpbl.v
    3ad2ant1
    #
    ercpbl.f
    wph
    @0
    @1
    @3
    simp2l
    ercpbllem
    @4
    vx
    cB
    cD
    c.sm
    cF
    cV
    @11
    @12
    ercpbl.f
    wph
    @0
    @1
    @3
    simp2r
    ercpbllem
    anbi12d
    wph
    @2
    @9
    @10
    wi
    @3
    erlecpbl.e
    3ad2ant1
    sylbid
end

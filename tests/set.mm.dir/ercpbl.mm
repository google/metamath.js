include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "3ad2ant1.mm"
include "wer.mm"
include "cvv.mm"
include "simp2l.mm"
include "ercpbllem.mm"
include "simp2r.mm"
include "anbi12d.mm"
include "caovclg.mm"
include "3adant3.mm"
include "3imtr4d.mm"

theorem ercpbl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.sm: class .~
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume ercpbl.r: |- ( ph -> .~ Er V )
  assume ercpbl.v: |- ( ph -> V e. _V )
  assume ercpbl.f: |- F = ( x e. V |-> [ x ] .~ )
  assume ercpbl.c: |- ( ( ph /\ ( a e. V /\ b e. V ) ) -> ( a .+ b ) e. V )
  assume ercpbl.e: |- ( ph -> ( ( A .~ C /\ B .~ D ) -> ( A .+ B ) .~ ( C .+ D ) ) )

  disjoint .~ x
  disjoint a b
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint A x
  disjoint B b
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint V a
  disjoint V b
  disjoint V x
  disjoint .+ a
  disjoint .+ b
  disjoint .+ x
  disjoint a ph
  disjoint b ph
  disjoint ph x
  assert |- ( ( ph /\ ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( ( ( F ` A ) = ( F ` C ) /\ ( F ` B ) = ( F ` D ) ) -> ( F ` ( A .+ B ) ) = ( F ` ( C .+ D ) ) ) )

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
    c.pl
    co
    #
    cC
    cD
    c.pl
    co
    #
    c.sm
    wbr
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
    @8
    cF
    cfv
    @9
    cF
    cfv
    wceq
    wph
    @2
    @7
    @10
    wi
    @3
    ercpbl.e
    3ad2ant1
    @4
    @11
    @5
    @12
    @6
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
    @13
    @14
    ercpbl.f
    wph
    @0
    @1
    @3
    simp2r
    ercpbllem
    anbi12d
    @4
    vx
    @8
    @9
    c.sm
    cF
    cV
    @13
    @14
    ercpbl.f
    wph
    @2
    @8
    cV
    wcel
    @3
    wph
    va
    vb
    cA
    cB
    cV
    cV
    cV
    c.pl
    ercpbl.c
    caovclg
    3adant3
    ercpbllem
    3imtr4d
end

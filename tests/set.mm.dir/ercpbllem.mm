include "cfv.mm"
include "wceq.mm"
include "cec.mm"
include "wbr.mm"
include "divsfval.mm"
include "eqeq12d.mm"
include "erth.mm"
include "bitr4d.mm"

theorem ercpbllem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.sm: class .~
  let cF: class F
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let cD: class D
  let c.pl: class .+
  assume ercpbl.r: |- ( ph -> .~ Er V )
  assume ercpbl.v: |- ( ph -> V e. _V )
  assume ercpbl.f: |- F = ( x e. V |-> [ x ] .~ )
  assume ercpbllem.1: |- ( ph -> A e. V )

  disjoint .~ x
  disjoint A x
  disjoint B x
  disjoint V x
  disjoint ph x
  disjoint a b
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint B b
  disjoint C x
  disjoint D x
  disjoint V a
  disjoint V b
  disjoint .+ a
  disjoint .+ b
  disjoint .+ x
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( ( F ` A ) = ( F ` B ) <-> A .~ B ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    wceq
    cA
    c.sm
    cec
    #
    cB
    c.sm
    cec
    #
    wceq
    cA
    cB
    c.sm
    wbr
    wph
    @0
    @2
    @1
    @3
    wph
    vx
    cA
    c.sm
    cF
    cV
    ercpbl.r
    ercpbl.v
    ercpbl.f
    divsfval
    wph
    vx
    cB
    c.sm
    cF
    cV
    ercpbl.r
    ercpbl.v
    ercpbl.f
    divsfval
    eqeq12d
    wph
    cA
    cB
    c.sm
    cV
    ercpbl.r
    ercpbllem.1
    erth
    bitr4d
end

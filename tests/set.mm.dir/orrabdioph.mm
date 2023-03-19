include "cn0.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "crab.mm"
include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "cun.mm"
include "unrab.mm"
include "diophun.mm"
include "syl5eqelr.mm"

theorem orrabdioph
  let wph: wff ph
  let wps: wff ps
  let vt: setvar t
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let cA: class A
  let cB: class B

  disjoint N t
  disjoint N a
  disjoint N b
  disjoint a t
  disjoint b t
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  assert |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N ) /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | ( ph \/ ps ) } e. ( Dioph ` N ) )

  proof
    wph
    vt
    cn0
    c1
    cN
    cfz
    co
    cmap
    co
    #
    crab
    #
    cN
    cdioph
    cfv
    #
    wcel
    wps
    vt
    @0
    crab
    #
    @2
    wcel
    wa
    wph
    wps
    wo
    vt
    @0
    crab
    @1
    @3
    cun
    @2
    wph
    wps
    vt
    @0
    unrab
    @1
    @3
    cN
    diophun
    syl5eqelr
end

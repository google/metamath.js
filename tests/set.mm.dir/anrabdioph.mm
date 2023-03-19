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
include "cin.mm"
include "inrab.mm"
include "diophin.mm"
include "syl5eqelr.mm"

theorem anrabdioph
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
  assert |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N ) /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | ( ph /\ ps ) } e. ( Dioph ` N ) )

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
    wa
    vt
    @0
    crab
    @1
    @3
    cin
    @2
    wph
    wps
    vt
    @0
    inrab
    @1
    @3
    cN
    diophin
    syl5eqelr
end

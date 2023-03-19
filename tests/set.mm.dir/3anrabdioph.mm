include "cn0.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "crab.mm"
include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "rabbii.mm"
include "anrabdioph.mm"
include "sylan.mm"
include "syl5eqel.mm"
include "3impa.mm"

theorem 3anrabdioph
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
  assert |- ( ( { t e. ( NN0 ^m ( 1 ... N ) ) | ph } e. ( Dioph ` N ) /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ps } e. ( Dioph ` N ) /\ { t e. ( NN0 ^m ( 1 ... N ) ) | ch } e. ( Dioph ` N ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | ( ph /\ ps /\ ch ) } e. ( Dioph ` N ) )

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
    cN
    cdioph
    cfv
    #
    wcel
    #
    wps
    vt
    @0
    crab
    @1
    wcel
    #
    wch
    vt
    @0
    crab
    @1
    wcel
    #
    wph
    wps
    wch
    w3a
    #
    vt
    @0
    crab
    #
    @1
    wcel
    @2
    @3
    wa
    #
    @4
    wa
    @6
    wph
    wps
    wa
    #
    wch
    wa
    #
    vt
    @0
    crab
    #
    @1
    @5
    @9
    vt
    @0
    wph
    wps
    wch
    df-3an
    rabbii
    @7
    @8
    vt
    @0
    crab
    @1
    wcel
    @4
    @10
    @1
    wcel
    wph
    wps
    vt
    cN
    anrabdioph
    @8
    wch
    vt
    cN
    anrabdioph
    sylan
    syl5eqel
    3impa
end

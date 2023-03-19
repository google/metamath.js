include "cdit.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cif.mm"
include "df-ditg.mm"
include "iftrued.mm"
include "syl5eq.mm"
include "itgeq2dv.mm"
include "syl5req.mm"
include "3eqtrd.mm"

theorem ditgeq3d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let vk: setvar k
  assume ditgeq3d.1: |- ( ph -> A <_ B )
  assume ditgeq3d.2: |- ( ( ph /\ x e. ( A (,) B ) ) -> D = E )

  disjoint ph x
  disjoint k x
  assert |- ( ph -> S_ [ A -> B ] D _d x = S_ [ A -> B ] E _d x )

  proof
    wph
    vx
    cA
    cB
    cD
    cdit
    #
    vx
    cA
    cB
    cioo
    co
    #
    cD
    citg
    #
    vx
    @1
    cE
    citg
    #
    vx
    cA
    cB
    cE
    cdit
    #
    wph
    @0
    cA
    cB
    cle
    wbr
    #
    @2
    vx
    cB
    cA
    cioo
    co
    #
    cD
    citg
    cneg
    #
    cif
    @2
    vx
    cA
    cB
    cD
    df-ditg
    wph
    @5
    @2
    @7
    ditgeq3d.1
    iftrued
    syl5eq
    wph
    vx
    @1
    cD
    cE
    ditgeq3d.2
    itgeq2dv
    wph
    @4
    @5
    @3
    vx
    @6
    cE
    citg
    cneg
    #
    cif
    @3
    vx
    cA
    cB
    cE
    df-ditg
    wph
    @5
    @3
    @8
    ditgeq3d.1
    iftrued
    syl5req
    3eqtrd
end

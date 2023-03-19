include "cdit.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "cif.mm"
include "df-ditg.mm"
include "iftrued.mm"
include "syl5eq.mm"

theorem ditgpos
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ditgpos.1: |- ( ph -> A <_ B )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> S_ [ A -> B ] C _d x = S. ( A (,) B ) C _d x )

  proof
    wph
    vx
    cA
    cB
    cC
    cdit
    cA
    cB
    cle
    wbr
    #
    vx
    cA
    cB
    cioo
    co
    cC
    citg
    #
    vx
    cB
    cA
    cioo
    co
    cC
    citg
    cneg
    #
    cif
    @1
    vx
    cA
    cB
    cC
    df-ditg
    wph
    @0
    @1
    @2
    ditgpos.1
    iftrued
    syl5eq
end

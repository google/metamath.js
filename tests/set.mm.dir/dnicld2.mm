include "cfv.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cmin.mm"
include "cabs.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "dnival.mm"
include "syl.mm"
include "dnicld1.mm"
include "eqeltrd.mm"

theorem dnicld2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cT: class T
  assume dnicld2.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnicld2.2: |- ( ph -> A e. RR )

  disjoint A x
  assert |- ( ph -> ( T ` A ) e. RR )

  proof
    wph
    cA
    cT
    cfv
    #
    cA
    c1
    c2
    cdiv
    co
    caddc
    co
    cfl
    cfv
    cA
    cmin
    co
    cabs
    cfv
    #
    cr
    wph
    cA
    cr
    wcel
    @0
    @1
    wceq
    dnicld2.2
    vx
    cA
    cT
    dnicld2.1
    dnival
    syl
    wph
    cA
    dnicld2.2
    dnicld1
    eqeltrd
end

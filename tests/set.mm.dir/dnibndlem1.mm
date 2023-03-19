include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cfl.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "dnival.mm"
include "syl.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"

theorem dnibndlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  assume dnibndlem1.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnibndlem1.2: |- ( ph -> A e. RR )
  assume dnibndlem1.3: |- ( ph -> B e. RR )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( ( abs ` ( ( T ` B ) - ( T ` A ) ) ) <_ S <-> ( abs ` ( ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) ) <_ S ) )

  proof
    wph
    cB
    cT
    cfv
    #
    cA
    cT
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    cB
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    cfl
    cfv
    cB
    cmin
    co
    cabs
    cfv
    #
    cA
    @3
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
    cmin
    co
    #
    cabs
    cfv
    cS
    cle
    wph
    @2
    @6
    cabs
    wph
    @0
    @4
    @1
    @5
    cmin
    wph
    cB
    cr
    wcel
    @0
    @4
    wceq
    dnibndlem1.3
    vx
    cB
    cT
    dnibndlem1.1
    dnival
    syl
    wph
    cA
    cr
    wcel
    @1
    @5
    wceq
    dnibndlem1.2
    vx
    cA
    cT
    dnibndlem1.1
    dnival
    syl
    oveq12d
    fveq2d
    breq1d
end

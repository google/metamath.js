include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "wn.mm"
include "cun.mm"
include "wo.mm"
include "crab.mm"
include "cif.mm"
include "unab.mm"
include "df-rab.mm"
include "uneq12i.mm"
include "df-if.mm"
include "3eqtr4ri.mm"

theorem dfif6
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint ph x
  disjoint A x
  disjoint B x
  disjoint C x
  assert |- if ( ph , A , B ) = ( { x e. A | ph } u. { x e. B | -. ph } )

  proof
    vx
    cv
    #
    cA
    wcel
    wph
    wa
    #
    vx
    cab
    #
    @0
    cB
    wcel
    wph
    wn
    #
    wa
    #
    vx
    cab
    #
    cun
    @1
    @4
    wo
    vx
    cab
    wph
    vx
    cA
    crab
    #
    @3
    vx
    cB
    crab
    #
    cun
    wph
    cA
    cB
    cif
    @1
    @4
    vx
    unab
    @6
    @2
    @7
    @5
    wph
    vx
    cA
    df-rab
    @3
    vx
    cB
    df-rab
    uneq12i
    wph
    vx
    cA
    cB
    df-if
    3eqtr4ri
end

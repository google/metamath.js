include "wa.mm"
include "wrex.mm"
include "w3a.mm"
include "r19.41v.mm"
include "reeanv.mm"
include "anbi1i.mm"
include "bitri.mm"
include "df-3an.mm"
include "2rexbii.mm"
include "rexbii.mm"
include "3bitr4i.mm"

theorem 3reeanv
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint ph y
  disjoint ph z
  disjoint y z
  disjoint ps x
  disjoint ps z
  disjoint x z
  disjoint ch x
  disjoint ch y
  disjoint x y
  disjoint A y
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C y
  assert |- ( E. x e. A E. y e. B E. z e. C ( ph /\ ps /\ ch ) <-> ( E. x e. A ph /\ E. y e. B ps /\ E. z e. C ch ) )

  proof
    wph
    wps
    wa
    #
    vy
    cB
    wrex
    #
    wch
    vz
    cC
    wrex
    #
    wa
    #
    vx
    cA
    wrex
    #
    wph
    vx
    cA
    wrex
    #
    wps
    vy
    cB
    wrex
    #
    wa
    #
    @2
    wa
    #
    wph
    wps
    wch
    w3a
    #
    vz
    cC
    wrex
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    @5
    @6
    @2
    w3a
    @4
    @1
    vx
    cA
    wrex
    #
    @2
    wa
    @8
    @1
    @2
    vx
    cA
    r19.41v
    @11
    @7
    @2
    wph
    wps
    vx
    vy
    cA
    cB
    reeanv
    anbi1i
    bitri
    @10
    @3
    vx
    cA
    @10
    @0
    wch
    wa
    #
    vz
    cC
    wrex
    vy
    cB
    wrex
    @3
    @9
    @12
    vy
    vz
    cB
    cC
    wph
    wps
    wch
    df-3an
    2rexbii
    @0
    wch
    vy
    vz
    cB
    cC
    reeanv
    bitri
    rexbii
    @5
    @6
    @2
    df-3an
    3bitr4i
end

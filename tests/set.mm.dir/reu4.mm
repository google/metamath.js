include "wreu.mm"
include "wrex.mm"
include "wrmo.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "reu5.mm"
include "rmo4.mm"
include "anbi2i.mm"
include "bitri.mm"

theorem reu4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume rmo4.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint ph z
  disjoint ps z
  assert |- ( E! x e. A ph <-> ( E. x e. A ph /\ A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) )

  proof
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    wrex
    #
    wph
    vx
    cA
    wrmo
    #
    wa
    @0
    wph
    wps
    wa
    vx
    vy
    weq
    wi
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    wph
    vx
    cA
    reu5
    @1
    @2
    @0
    wph
    wps
    vx
    vy
    cA
    rmo4.1
    rmo4
    anbi2i
    bitri
end

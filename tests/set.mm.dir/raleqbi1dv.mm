include "wceq.mm"
include "wral.mm"
include "raleq.mm"
include "ralbidv.mm"
include "bitrd.mm"

theorem raleqbi1dv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raleqd.1: |- ( A = B -> ( ph <-> ps ) )

  disjoint A x
  disjoint B x
  assert |- ( A = B -> ( A. x e. A ph <-> A. x e. B ps ) )

  proof
    cA
    cB
    wceq
    #
    wph
    vx
    cA
    wral
    wph
    vx
    cB
    wral
    wps
    vx
    cB
    wral
    wph
    vx
    cA
    cB
    raleq
    @0
    wph
    wps
    vx
    cB
    raleqd.1
    ralbidv
    bitrd
end

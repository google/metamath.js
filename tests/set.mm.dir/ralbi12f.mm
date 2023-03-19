include "wb.mm"
include "wral.mm"
include "wceq.mm"
include "ralbi.mm"
include "raleqf.mm"
include "sylan9bbr.mm"

theorem ralbi12f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume ralbi12f.1: |- F/_ x A
  assume ralbi12f.2: |- F/_ x B


  assert |- ( ( A = B /\ A. x e. A ( ph <-> ps ) ) -> ( A. x e. A ph <-> A. x e. B ps ) )

  proof
    wph
    wps
    wb
    vx
    cA
    wral
    wph
    vx
    cA
    wral
    wps
    vx
    cA
    wral
    cA
    cB
    wceq
    wps
    vx
    cB
    wral
    wph
    wps
    vx
    cA
    ralbi
    wps
    vx
    cA
    cB
    ralbi12f.1
    ralbi12f.2
    raleqf
    sylan9bbr
end

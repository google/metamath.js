include "cvv.mm"
include "wcel.mm"
include "wreu.mm"
include "crio.mm"
include "wb.mm"
include "riotaclbgBAD.mm"
include "ax-mp.mm"

theorem riotaclbBAD
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  assume riotaclb.1: |- A e. _V

  disjoint A x
  assert |- ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A )

  proof
    cA
    cvv
    wcel
    wph
    vx
    cA
    wreu
    wph
    vx
    cA
    crio
    cA
    wcel
    wb
    riotaclb.1
    wph
    vx
    cA
    cvv
    riotaclbgBAD
    ax-mp
end

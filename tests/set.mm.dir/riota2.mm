include "nfcv.mm"
include "nfv.mm"
include "riota2f.mm"

theorem riota2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume riota2.1: |- ( x = B -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  disjoint B x
  assert |- ( ( B e. A /\ E! x e. A ph ) -> ( ps <-> ( iota_ x e. A ph ) = B ) )

  proof
    wph
    wps
    vx
    cA
    cB
    vx
    cB
    nfcv
    wps
    vx
    nfv
    riota2.1
    riota2f
end

include "nfcvd.mm"
include "riota5f.mm"

theorem riota5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume riota5.1: |- ( ph -> B e. A )
  assume riota5.2: |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( iota_ x e. A ps ) = B )

  proof
    wph
    wps
    vx
    cA
    cB
    wph
    vx
    cB
    nfcvd
    riota5.1
    riota5.2
    riota5f
end

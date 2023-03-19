include "nfcv.mm"
include "nfv.mm"
include "elab3gf.mm"

theorem elab3g
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elab3g.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  assert |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) )

  proof
    wph
    wps
    vx
    cA
    cB
    vx
    cA
    nfcv
    wps
    vx
    nfv
    elab3g.1
    elab3gf
end

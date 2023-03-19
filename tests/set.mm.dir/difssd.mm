include "cdif.mm"
include "wss.mm"
include "difss.mm"
include "a1i.mm"

theorem difssd
  let wph: wff ph
  let cA: class A
  let cB: class B


  assert |- ( ph -> ( A \ B ) C_ A )

  proof
    cA
    cB
    cdif
    cA
    wss
    wph
    cA
    cB
    difss
    a1i
end

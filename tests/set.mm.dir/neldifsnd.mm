include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "neldifsn.mm"
include "a1i.mm"

theorem neldifsnd
  let wph: wff ph
  let cA: class A
  let cB: class B


  assert |- ( ph -> -. A e. ( B \ { A } ) )

  proof
    cA
    cB
    cA
    csn
    cdif
    wcel
    wn
    wph
    cA
    cB
    neldifsn
    a1i
end

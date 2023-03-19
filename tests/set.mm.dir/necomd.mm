include "wne.mm"
include "necom.mm"
include "sylib.mm"

theorem necomd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume necomd.1: |- ( ph -> A =/= B )


  assert |- ( ph -> B =/= A )

  proof
    wph
    cA
    cB
    wne
    cB
    cA
    wne
    necomd.1
    cA
    cB
    necom
    sylib
end

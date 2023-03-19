include "xrgtned.mm"
include "necomd.mm"

theorem xrltned
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xrltned.1: |- ( ph -> A e. RR* )
  assume xrltned.2: |- ( ph -> B e. RR* )
  assume xrltned.3: |- ( ph -> A < B )


  assert |- ( ph -> A =/= B )

  proof
    wph
    cB
    cA
    wph
    cA
    cB
    xrltned.1
    xrltned.2
    xrltned.3
    xrgtned
    necomd
end

include "cdif.mm"
include "wss.mm"
include "difss2.mm"
include "syl.mm"

theorem difss2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume difss2d.1: |- ( ph -> A C_ ( B \ C ) )


  assert |- ( ph -> A C_ B )

  proof
    wph
    cA
    cB
    cC
    cdif
    wss
    cA
    cB
    wss
    difss2d.1
    cA
    cB
    cC
    difss2
    syl
end

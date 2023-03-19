include "nfv.mm"
include "csbeq2d.mm"

theorem csbeq2dv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume csbeq2dv.1: |- ( ph -> B = C )

  disjoint ph x
  assert |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C )

  proof
    wph
    vx
    cA
    cB
    cC
    wph
    vx
    nfv
    csbeq2dv.1
    csbeq2d
end

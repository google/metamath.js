include "wceq.mm"
include "csb.mm"
include "csbeq1.mm"
include "syl.mm"

theorem csbeq1d
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume csbeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> [_ A / x ]_ C = [_ B / x ]_ C )

  proof
    wph
    cA
    cB
    wceq
    vx
    cA
    cC
    csb
    vx
    cB
    cC
    csb
    wceq
    csbeq1d.1
    vx
    cA
    cB
    cC
    csbeq1
    syl
end

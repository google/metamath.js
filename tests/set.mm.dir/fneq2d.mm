include "wceq.mm"
include "wfn.mm"
include "wb.mm"
include "fneq2.mm"
include "syl.mm"

theorem fneq2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume fneq2d.1: |- ( ph -> A = B )


  assert |- ( ph -> ( F Fn A <-> F Fn B ) )

  proof
    wph
    cA
    cB
    wceq
    cF
    cA
    wfn
    cF
    cB
    wfn
    wb
    fneq2d.1
    cA
    cB
    cF
    fneq2
    syl
end

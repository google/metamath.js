include "wceq.mm"
include "wfn.mm"
include "wb.mm"
include "fneq1.mm"
include "syl.mm"

theorem fneq1d
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  assume fneq1d.1: |- ( ph -> F = G )


  assert |- ( ph -> ( F Fn A <-> G Fn A ) )

  proof
    wph
    cF
    cG
    wceq
    cF
    cA
    wfn
    cG
    cA
    wfn
    wb
    fneq1d.1
    cA
    cF
    cG
    fneq1
    syl
end

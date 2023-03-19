include "wcel.mm"
include "csn.mm"
include "c0.mm"
include "wne.mm"
include "snnzg.mm"
include "syl.mm"

theorem snn0d
  let wph: wff ph
  let cA: class A
  let cV: class V
  assume snn0d.1: |- ( ph -> A e. V )


  assert |- ( ph -> { A } =/= (/) )

  proof
    wph
    cA
    cV
    wcel
    cA
    csn
    c0
    wne
    snn0d.1
    cA
    cV
    snnzg
    syl
end

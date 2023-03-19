include "eqcomd.mm"
include "eleqtrd.mm"

theorem eleqtrrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eleqtrrd.1: |- ( ph -> A e. B )
  assume eleqtrrd.2: |- ( ph -> C = B )


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    eleqtrrd.1
    wph
    cC
    cB
    eleqtrrd.2
    eqcomd
    eleqtrd
end

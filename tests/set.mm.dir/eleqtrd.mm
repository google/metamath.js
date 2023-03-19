include "wcel.mm"
include "eleq2d.mm"
include "mpbid.mm"

theorem eleqtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eleqtrd.1: |- ( ph -> A e. B )
  assume eleqtrd.2: |- ( ph -> B = C )


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    wcel
    cA
    cC
    wcel
    eleqtrd.1
    wph
    cB
    cC
    cA
    eleqtrd.2
    eleq2d
    mpbid
end

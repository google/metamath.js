include "eqcomd.mm"
include "syl5eleq.mm"

theorem syl5eleqr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume syl5eleqr.1: |- A e. B
  assume syl5eleqr.2: |- ( ph -> C = B )


  assert |- ( ph -> A e. C )

  proof
    wph
    cA
    cB
    cC
    syl5eleqr.1
    wph
    cC
    cB
    syl5eleqr.2
    eqcomd
    syl5eleq
end

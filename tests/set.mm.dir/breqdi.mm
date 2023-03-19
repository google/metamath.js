include "wbr.mm"
include "breqd.mm"
include "mpbid.mm"

theorem breqdi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume breq1d.1: |- ( ph -> A = B )
  assume breqdi.1: |- ( ph -> C A D )


  assert |- ( ph -> C B D )

  proof
    wph
    cC
    cD
    cA
    wbr
    cC
    cD
    cB
    wbr
    breqdi.1
    wph
    cA
    cB
    cC
    cD
    breq1d.1
    breqd
    mpbid
end

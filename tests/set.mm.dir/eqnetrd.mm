include "wne.mm"
include "neeq1d.mm"
include "mpbird.mm"

theorem eqnetrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqnetrd.1: |- ( ph -> A = B )
  assume eqnetrd.2: |- ( ph -> B =/= C )


  assert |- ( ph -> A =/= C )

  proof
    wph
    cA
    cC
    wne
    cB
    cC
    wne
    eqnetrd.2
    wph
    cA
    cB
    cC
    eqnetrd.1
    neeq1d
    mpbird
end

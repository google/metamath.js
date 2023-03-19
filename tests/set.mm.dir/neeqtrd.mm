include "wne.mm"
include "neeq2d.mm"
include "mpbid.mm"

theorem neeqtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume neeqtrd.1: |- ( ph -> A =/= B )
  assume neeqtrd.2: |- ( ph -> B = C )


  assert |- ( ph -> A =/= C )

  proof
    wph
    cA
    cB
    wne
    cA
    cC
    wne
    neeqtrd.1
    wph
    cB
    cC
    cA
    neeqtrd.2
    neeq2d
    mpbid
end

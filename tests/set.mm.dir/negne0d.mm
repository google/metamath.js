include "cc0.mm"
include "wne.mm"
include "cneg.mm"
include "negne0bd.mm"
include "mpbid.mm"

theorem negne0d
  let wph: wff ph
  let cA: class A
  assume negidd.1: |- ( ph -> A e. CC )
  assume negne0d.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> -u A =/= 0 )

  proof
    wph
    cA
    cc0
    wne
    cA
    cneg
    cc0
    wne
    negne0d.2
    wph
    cA
    negidd.1
    negne0bd
    mpbid
end

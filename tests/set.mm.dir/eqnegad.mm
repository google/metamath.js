include "cneg.mm"
include "wceq.mm"
include "cc0.mm"
include "eqnegd.mm"
include "mpbid.mm"

theorem eqnegad
  let wph: wff ph
  let cA: class A
  assume eqnegad.1: |- ( ph -> A e. CC )
  assume eqnegad.2: |- ( ph -> A = -u A )


  assert |- ( ph -> A = 0 )

  proof
    wph
    cA
    cA
    cneg
    wceq
    cA
    cc0
    wceq
    eqnegad.2
    wph
    cA
    eqnegad.1
    eqnegd
    mpbid
end

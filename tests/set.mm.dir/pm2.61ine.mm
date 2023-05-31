include "wne.mm"
include "wn.mm"
include "wceq.mm"
include "nne.mm"
include "sylbi.mm"
include "pm2.61i.mm"

theorem pm2.61ine
  param wph: wff ph
  param cA: class A
  param cB: class B
  assume pm2.61ine.1: |- ( A = B -> ph )
  assume pm2.61ine.2: |- ( A =/= B -> ph )


  assert |- ph

  proof
    cA
    cB
    wne
    #
    wph
    pm2.61ine.2
    @0
    wn
    cA
    cB
    wceq
    wph
    cA
    cB
    nne
    pm2.61ine.1
    sylbi
    pm2.61i
end

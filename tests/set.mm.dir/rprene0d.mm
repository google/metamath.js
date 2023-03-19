include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "rpred.mm"
include "rpne0d.mm"
include "jca.mm"

theorem rprene0d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( A e. RR /\ A =/= 0 ) )

  proof
    wph
    cA
    cr
    wcel
    cA
    cc0
    wne
    wph
    cA
    rpred.1
    rpred
    wph
    cA
    rpred.1
    rpne0d
    jca
end

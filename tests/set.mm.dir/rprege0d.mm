include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "rpred.mm"
include "rpge0d.mm"
include "jca.mm"

theorem rprege0d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( A e. RR /\ 0 <_ A ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wph
    cA
    rpred.1
    rpred
    wph
    cA
    rpred.1
    rpge0d
    jca
end

include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "jca.mm"

theorem rpregt0d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( A e. RR /\ 0 < A ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    wph
    cA
    rpred.1
    rpred
    wph
    cA
    rpred.1
    rpgt0d
    jca
end

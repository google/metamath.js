include "cr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wne.mm"
include "renepnf.mm"
include "syl.mm"

theorem renepnfd
  let wph: wff ph
  let cA: class A
  assume rexrd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A =/= +oo )

  proof
    wph
    cA
    cr
    wcel
    cA
    cpnf
    wne
    rexrd.1
    cA
    renepnf
    syl
end

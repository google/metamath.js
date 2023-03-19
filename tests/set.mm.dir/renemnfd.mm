include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "wne.mm"
include "renemnf.mm"
include "syl.mm"

theorem renemnfd
  let wph: wff ph
  let cA: class A
  assume rexrd.1: |- ( ph -> A e. RR )


  assert |- ( ph -> A =/= -oo )

  proof
    wph
    cA
    cr
    wcel
    cA
    cmnf
    wne
    rexrd.1
    cA
    renemnf
    syl
end

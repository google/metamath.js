include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0.mm"
include "syl.mm"

theorem rpne0d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> A =/= 0 )

  proof
    wph
    cA
    crp
    wcel
    cA
    cc0
    wne
    rpred.1
    cA
    rpne0
    syl
end

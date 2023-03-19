include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "recne0.mm"
include "syl2anc.mm"

theorem recne0d
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )
  assume reccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( 1 / A ) =/= 0 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    c1
    cA
    cdiv
    co
    cc0
    wne
    div1d.1
    reccld.2
    cA
    recne0
    syl2anc
end

include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "reccl.mm"
include "syl2anc.mm"

theorem reccld
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )
  assume reccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( 1 / A ) e. CC )

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
    cc
    wcel
    div1d.1
    reccld.2
    cA
    reccl
    syl2anc
end

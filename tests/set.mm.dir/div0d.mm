include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "div0.mm"
include "syl2anc.mm"

theorem div0d
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )
  assume reccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( 0 / A ) = 0 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cc0
    cA
    cdiv
    co
    cc0
    wceq
    div1d.1
    reccld.2
    cA
    div0
    syl2anc
end

include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "recid2.mm"
include "syl2anc.mm"

theorem recid2d
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )
  assume reccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( ( 1 / A ) x. A ) = 1 )

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
    cA
    cmul
    co
    c1
    wceq
    div1d.1
    reccld.2
    cA
    recid2
    syl2anc
end

include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "divid.mm"
include "syl2anc.mm"

theorem dividd
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )
  assume reccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( A / A ) = 1 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cA
    cA
    cdiv
    co
    c1
    wceq
    div1d.1
    reccld.2
    cA
    divid
    syl2anc
end

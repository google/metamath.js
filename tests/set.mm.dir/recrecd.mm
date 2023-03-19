include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "recrec.mm"
include "syl2anc.mm"

theorem recrecd
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )
  assume reccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( 1 / ( 1 / A ) ) = A )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    c1
    c1
    cA
    cdiv
    co
    cdiv
    co
    cA
    wceq
    div1d.1
    reccld.2
    cA
    recrec
    syl2anc
end

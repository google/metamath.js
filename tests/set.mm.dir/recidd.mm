include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "recid.mm"
include "syl2anc.mm"

theorem recidd
  let wph: wff ph
  let cA: class A
  assume div1d.1: |- ( ph -> A e. CC )
  assume reccld.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( A x. ( 1 / A ) ) = 1 )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cA
    c1
    cA
    cdiv
    co
    cmul
    co
    c1
    wceq
    div1d.1
    reccld.2
    cA
    recid
    syl2anc
end

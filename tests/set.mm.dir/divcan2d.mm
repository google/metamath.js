include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "divcan2.mm"
include "syl3anc.mm"

theorem divcan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divcld.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( B x. ( A / B ) ) = A )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    cB
    cA
    cB
    cdiv
    co
    cmul
    co
    cA
    wceq
    div1d.1
    divcld.2
    divcld.3
    cA
    cB
    divcan2
    syl3anc
end

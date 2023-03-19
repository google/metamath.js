include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "divrec.mm"
include "syl3anc.mm"

theorem divrecd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divcld.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( A / B ) = ( A x. ( 1 / B ) ) )

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
    cA
    cB
    cdiv
    co
    cA
    c1
    cB
    cdiv
    co
    cmul
    co
    wceq
    div1d.1
    divcld.2
    divcld.3
    cA
    cB
    divrec
    syl3anc
end

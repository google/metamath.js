include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "divne0b.mm"
include "syl3anc.mm"

theorem divne0bd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divcld.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( A =/= 0 <-> ( A / B ) =/= 0 ) )

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
    cc0
    wne
    cA
    cB
    cdiv
    co
    cc0
    wne
    wb
    div1d.1
    divcld.2
    divcld.3
    cA
    cB
    divne0b
    syl3anc
end

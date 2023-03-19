include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "divneg.mm"
include "syl3anc.mm"

theorem divnegd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divcld.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> -u ( A / B ) = ( -u A / B ) )

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
    cneg
    cA
    cneg
    cB
    cdiv
    co
    wceq
    div1d.1
    divcld.2
    divcld.3
    cA
    cB
    divneg
    syl3anc
end

include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cneg.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "div2neg.mm"
include "syl3anc.mm"

theorem div2negd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divcld.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( -u A / -u B ) = ( A / B ) )

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
    cneg
    cB
    cneg
    cdiv
    co
    cA
    cB
    cdiv
    co
    wceq
    div1d.1
    divcld.2
    divcld.3
    cA
    cB
    div2neg
    syl3anc
end

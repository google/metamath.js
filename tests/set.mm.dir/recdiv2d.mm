include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "recdiv2.mm"
include "syl22anc.mm"

theorem recdiv2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divne0d.3: |- ( ph -> A =/= 0 )
  assume divne0d.4: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( ( 1 / A ) / B ) = ( 1 / ( A x. B ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cB
    cc
    wcel
    cB
    cc0
    wne
    c1
    cA
    cdiv
    co
    cB
    cdiv
    co
    c1
    cA
    cB
    cmul
    co
    cdiv
    co
    wceq
    div1d.1
    divne0d.3
    divcld.2
    divne0d.4
    cA
    cB
    recdiv2
    syl22anc
end

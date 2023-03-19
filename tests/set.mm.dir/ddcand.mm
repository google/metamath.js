include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "ddcan.mm"
include "syl22anc.mm"

theorem ddcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divne0d.3: |- ( ph -> A =/= 0 )
  assume divne0d.4: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( A / ( A / B ) ) = B )

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
    cA
    cA
    cB
    cdiv
    co
    cdiv
    co
    cB
    wceq
    div1d.1
    divne0d.3
    divcld.2
    divne0d.4
    cA
    cB
    ddcan
    syl22anc
end

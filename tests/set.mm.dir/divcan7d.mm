include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "divcan7.mm"
include "syl122anc.mm"

theorem divcan7d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )
  assume divdiv23d.5: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A / C ) / ( B / C ) ) = ( A / B ) )

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
    cC
    cc
    wcel
    cC
    cc0
    wne
    cA
    cC
    cdiv
    co
    cB
    cC
    cdiv
    co
    cdiv
    co
    cA
    cB
    cdiv
    co
    wceq
    div1d.1
    divcld.2
    divmuld.4
    divmuld.3
    divdiv23d.5
    cA
    cB
    cC
    divcan7
    syl122anc
end

include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "divdiv1.mm"
include "syl122anc.mm"

theorem divdiv1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )
  assume divdiv23d.5: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A / B ) / C ) = ( A / ( B x. C ) ) )

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
    cB
    cdiv
    co
    cC
    cdiv
    co
    cA
    cB
    cC
    cmul
    co
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
    divdiv1
    syl122anc
end

include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "divdiv2.mm"
include "syl122anc.mm"

theorem divdiv2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )
  assume divdiv23d.5: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( A / ( B / C ) ) = ( ( A x. C ) / B ) )

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
    cC
    cdiv
    co
    cdiv
    co
    cA
    cC
    cmul
    co
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
    divdiv2
    syl122anc
end

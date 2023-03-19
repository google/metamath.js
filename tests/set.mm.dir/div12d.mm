include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "div12.mm"
include "syl112anc.mm"

theorem div12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divassd.4: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( A x. ( B / C ) ) = ( B x. ( A / C ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
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
    cmul
    co
    cB
    cA
    cC
    cdiv
    co
    cmul
    co
    wceq
    div1d.1
    divcld.2
    divmuld.3
    divassd.4
    cA
    cB
    cC
    div12
    syl112anc
end

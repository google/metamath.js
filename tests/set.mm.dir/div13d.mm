include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "div13.mm"
include "syl121anc.mm"

theorem div13d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( ( A / B ) x. C ) = ( ( C / B ) x. A ) )

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
    cA
    cB
    cdiv
    co
    cC
    cmul
    co
    cC
    cB
    cdiv
    co
    cA
    cmul
    co
    wceq
    div1d.1
    divcld.2
    divmuld.4
    divmuld.3
    cA
    cB
    cC
    div13
    syl121anc
end

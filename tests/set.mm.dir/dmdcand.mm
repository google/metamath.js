include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "dmdcan.mm"
include "syl221anc.mm"

theorem dmdcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )
  assume divdiv23d.5: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( B / C ) x. ( A / B ) ) = ( A / C ) )

  proof
    wph
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
    cc
    wcel
    cB
    cC
    cdiv
    co
    cA
    cB
    cdiv
    co
    cmul
    co
    cA
    cC
    cdiv
    co
    wceq
    divcld.2
    divmuld.4
    divmuld.3
    divdiv23d.5
    div1d.1
    cB
    cC
    cA
    dmdcan
    syl221anc
end

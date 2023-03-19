include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "wb.mm"
include "divmul.mm"
include "syl112anc.mm"

theorem divmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( ( A / B ) = C <-> ( B x. C ) = A ) )

  proof
    wph
    cA
    cc
    wcel
    cC
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
    cC
    wceq
    cB
    cC
    cmul
    co
    cA
    wceq
    wb
    div1d.1
    divmuld.3
    divcld.2
    divmuld.4
    cA
    cC
    cB
    divmul
    syl112anc
end

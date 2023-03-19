include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "wb.mm"
include "divmul2.mm"
include "syl112anc.mm"

theorem divmul2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divassd.4: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A / C ) = B <-> A = ( C x. B ) ) )

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
    cC
    cdiv
    co
    cB
    wceq
    cA
    cC
    cB
    cmul
    co
    wceq
    wb
    div1d.1
    divcld.2
    divmuld.3
    divassd.4
    cA
    cB
    cC
    divmul2
    syl112anc
end

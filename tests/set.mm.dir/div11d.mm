include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "div11.mm"
include "syl112anc.mm"
include "mpbid.mm"

theorem div11d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divassd.4: |- ( ph -> C =/= 0 )
  assume div11d.5: |- ( ph -> ( A / C ) = ( B / C ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cC
    cdiv
    co
    cB
    cC
    cdiv
    co
    wceq
    #
    cA
    cB
    wceq
    #
    div11d.5
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
    @0
    @1
    wb
    div1d.1
    divcld.2
    divmuld.3
    divassd.4
    cA
    cB
    cC
    div11
    syl112anc
    mpbid
end

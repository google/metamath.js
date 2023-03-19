include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "rec11.mm"
include "syl22anc.mm"
include "mpbid.mm"

theorem rec11d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divne0d.3: |- ( ph -> A =/= 0 )
  assume divne0d.4: |- ( ph -> B =/= 0 )
  assume rec11d.5: |- ( ph -> ( 1 / A ) = ( 1 / B ) )


  assert |- ( ph -> A = B )

  proof
    wph
    c1
    cA
    cdiv
    co
    c1
    cB
    cdiv
    co
    wceq
    #
    cA
    cB
    wceq
    #
    rec11d.5
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
    @0
    @1
    wb
    div1d.1
    divne0d.3
    divcld.2
    divne0d.4
    cA
    cB
    rec11
    syl22anc
    mpbid
end

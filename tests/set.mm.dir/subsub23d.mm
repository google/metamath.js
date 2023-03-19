include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "subsub23.mm"
include "syl3anc.mm"

theorem subsub23d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume subsub23d.1: |- ( ph -> A e. CC )
  assume subsub23d.2: |- ( ph -> B e. CC )
  assume subsub23d.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A - B ) = C <-> ( A - C ) = B ) )

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
    cA
    cB
    cmin
    co
    cC
    wceq
    cA
    cC
    cmin
    co
    cB
    wceq
    wb
    subsub23d.1
    subsub23d.2
    subsub23d.3
    cA
    cB
    cC
    subsub23
    syl3anc
end

include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "addcan2.mm"
include "syl3anc.mm"

theorem addcan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + C ) = ( B + C ) <-> A = B ) )

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
    cC
    caddc
    co
    cB
    cC
    caddc
    co
    wceq
    cA
    cB
    wceq
    wb
    muld.1
    addcomd.2
    addcand.3
    cA
    cB
    cC
    addcan2
    syl3anc
end

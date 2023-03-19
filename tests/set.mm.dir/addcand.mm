include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "addcan.mm"
include "syl3anc.mm"

theorem addcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume muld.1: |- ( ph -> A e. CC )
  assume addcomd.2: |- ( ph -> B e. CC )
  assume addcand.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + B ) = ( A + C ) <-> B = C ) )

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
    caddc
    co
    cA
    cC
    caddc
    co
    wceq
    cB
    cC
    wceq
    wb
    muld.1
    addcomd.2
    addcand.3
    cA
    cB
    cC
    addcan
    syl3anc
end

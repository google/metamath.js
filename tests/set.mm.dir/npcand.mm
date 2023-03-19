include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "npcan.mm"
include "syl2anc.mm"

theorem npcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A - B ) + B ) = A )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmin
    co
    cB
    caddc
    co
    cA
    wceq
    negidd.1
    pncand.2
    cA
    cB
    npcan
    syl2anc
end

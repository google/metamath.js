include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "pncan.mm"
include "syl2anc.mm"

theorem pncand
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A + B ) - B ) = A )

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
    caddc
    co
    cB
    cmin
    co
    cA
    wceq
    negidd.1
    pncand.2
    cA
    cB
    pncan
    syl2anc
end

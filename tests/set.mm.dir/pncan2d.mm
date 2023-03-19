include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "pncan2.mm"
include "syl2anc.mm"

theorem pncan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A + B ) - A ) = B )

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
    cA
    cmin
    co
    cB
    wceq
    negidd.1
    pncand.2
    cA
    cB
    pncan2
    syl2anc
end

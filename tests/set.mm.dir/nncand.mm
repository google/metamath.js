include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "nncan.mm"
include "syl2anc.mm"

theorem nncand
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A - ( A - B ) ) = B )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cA
    cB
    cmin
    co
    cmin
    co
    cB
    wceq
    negidd.1
    pncand.2
    cA
    cB
    nncan
    syl2anc
end

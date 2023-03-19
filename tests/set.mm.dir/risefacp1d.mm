include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crisefac.mm"
include "cmul.mm"
include "wceq.mm"
include "risefacp1.mm"
include "syl2anc.mm"

theorem risefacp1d
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume rffacp1d.1: |- ( ph -> A e. CC )
  assume rffacp1d.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A RiseFac ( N + 1 ) ) = ( ( A RiseFac N ) x. ( A + N ) ) )

  proof
    wph
    cA
    cc
    wcel
    cN
    cn0
    wcel
    cA
    cN
    c1
    caddc
    co
    crisefac
    co
    cA
    cN
    crisefac
    co
    cA
    cN
    caddc
    co
    cmul
    co
    wceq
    rffacp1d.1
    rffacp1d.2
    cA
    cN
    risefacp1
    syl2anc
end

include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfallfac.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "fallfacp1.mm"
include "syl2anc.mm"

theorem fallfacp1d
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume rffacp1d.1: |- ( ph -> A e. CC )
  assume rffacp1d.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A FallFac ( N + 1 ) ) = ( ( A FallFac N ) x. ( A - N ) ) )

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
    cfallfac
    co
    cA
    cN
    cfallfac
    co
    cA
    cN
    cmin
    co
    cmul
    co
    wceq
    rffacp1d.1
    rffacp1d.2
    cA
    cN
    fallfacp1
    syl2anc
end

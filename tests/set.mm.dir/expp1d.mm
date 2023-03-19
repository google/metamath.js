include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "expp1.mm"
include "syl2anc.mm"

theorem expp1d
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume expcld.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A ^ ( N + 1 ) ) = ( ( A ^ N ) x. A ) )

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
    cexp
    co
    cA
    cN
    cexp
    co
    cA
    cmul
    co
    wceq
    expcld.1
    expcld.2
    cA
    cN
    expp1
    syl2anc
end

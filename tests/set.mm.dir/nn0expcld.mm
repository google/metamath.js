include "cn0.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "nn0expcl.mm"
include "syl2anc.mm"

theorem nn0expcld
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume nn0expcld.1: |- ( ph -> A e. NN0 )
  assume nn0expcld.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A ^ N ) e. NN0 )

  proof
    wph
    cA
    cn0
    wcel
    cN
    cn0
    wcel
    cA
    cN
    cexp
    co
    cn0
    wcel
    nn0expcld.1
    nn0expcld.2
    cA
    cN
    nn0expcl
    syl2anc
end

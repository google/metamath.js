include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "expcl.mm"
include "syl2anc.mm"

theorem expcld
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume expcld.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A ^ N ) e. CC )

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
    cexp
    co
    cc
    wcel
    expcld.1
    expcld.2
    cA
    cN
    expcl
    syl2anc
end

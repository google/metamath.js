include "cn.mm"
include "wcel.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "nnexpcl.mm"
include "syl2anc.mm"

theorem nnexpcld
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume nnexpcld.1: |- ( ph -> A e. NN )
  assume nnexpcld.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A ^ N ) e. NN )

  proof
    wph
    cA
    cn
    wcel
    cN
    cn0
    wcel
    cA
    cN
    cexp
    co
    cn
    wcel
    nnexpcld.1
    nnexpcld.2
    cA
    cN
    nnexpcl
    syl2anc
end

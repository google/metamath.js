include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "cpc.mm"
include "co.mm"
include "cn0.mm"
include "pccl.mm"
include "syl2anc.mm"

theorem pccld
  let wph: wff ph
  let cP: class P
  let cN: class N
  assume pccld.1: |- ( ph -> P e. Prime )
  assume pccld.2: |- ( ph -> N e. NN )


  assert |- ( ph -> ( P pCnt N ) e. NN0 )

  proof
    wph
    cP
    cprime
    wcel
    cN
    cn
    wcel
    cP
    cN
    cpc
    co
    cn0
    wcel
    pccld.1
    pccld.2
    cP
    cN
    pccl
    syl2anc
end

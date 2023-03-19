include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "cbc.mm"
include "co.mm"
include "bccl.mm"
include "syl2anc.mm"

theorem bccld
  let wph: wff ph
  let cK: class K
  let cN: class N
  assume bccld.n: |- ( ph -> N e. NN0 )
  assume bccld.k: |- ( ph -> K e. ZZ )


  assert |- ( ph -> ( N _C K ) e. NN0 )

  proof
    wph
    cN
    cn0
    wcel
    cK
    cz
    wcel
    cN
    cK
    cbc
    co
    cn0
    wcel
    bccld.n
    bccld.k
    cK
    cN
    bccl
    syl2anc
end

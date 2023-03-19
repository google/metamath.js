include "cz.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "cn0.mm"
include "gcdcl.mm"
include "syl2anc.mm"

theorem gcdcld
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume gcdcld.1: |- ( ph -> M e. ZZ )
  assume gcdcld.2: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( M gcd N ) e. NN0 )

  proof
    wph
    cM
    cz
    wcel
    cN
    cz
    wcel
    cM
    cN
    cgcd
    co
    cn0
    wcel
    gcdcld.1
    gcdcld.2
    cM
    cN
    gcdcl
    syl2anc
end

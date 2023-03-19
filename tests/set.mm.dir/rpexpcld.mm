include "crp.mm"
include "wcel.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "rpexpcl.mm"
include "syl2anc.mm"

theorem rpexpcld
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume rpexpcld.1: |- ( ph -> A e. RR+ )
  assume rpexpcld.2: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( A ^ N ) e. RR+ )

  proof
    wph
    cA
    crp
    wcel
    cN
    cz
    wcel
    cA
    cN
    cexp
    co
    crp
    wcel
    rpexpcld.1
    rpexpcld.2
    cA
    cN
    rpexpcl
    syl2anc
end

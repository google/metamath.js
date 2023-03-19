include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "reexpcl.mm"
include "syl2anc.mm"

theorem reexpcld
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume reexpcld.1: |- ( ph -> A e. RR )
  assume reexpcld.2: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A ^ N ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cN
    cn0
    wcel
    cA
    cN
    cexp
    co
    cr
    wcel
    reexpcld.1
    reexpcld.2
    cA
    cN
    reexpcl
    syl2anc
end

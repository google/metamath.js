include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "expge1.mm"
include "syl3anc.mm"

theorem expge1d
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume reexpcld.1: |- ( ph -> A e. RR )
  assume reexpcld.2: |- ( ph -> N e. NN0 )
  assume expge1d.3: |- ( ph -> 1 <_ A )


  assert |- ( ph -> 1 <_ ( A ^ N ) )

  proof
    wph
    cA
    cr
    wcel
    cN
    cn0
    wcel
    c1
    cA
    cle
    wbr
    c1
    cA
    cN
    cexp
    co
    cle
    wbr
    reexpcld.1
    reexpcld.2
    expge1d.3
    cA
    cN
    expge1
    syl3anc
end

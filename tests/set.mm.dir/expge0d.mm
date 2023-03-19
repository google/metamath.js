include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cexp.mm"
include "co.mm"
include "expge0.mm"
include "syl3anc.mm"

theorem expge0d
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume reexpcld.1: |- ( ph -> A e. RR )
  assume reexpcld.2: |- ( ph -> N e. NN0 )
  assume expge0d.3: |- ( ph -> 0 <_ A )


  assert |- ( ph -> 0 <_ ( A ^ N ) )

  proof
    wph
    cA
    cr
    wcel
    cN
    cn0
    wcel
    cc0
    cA
    cle
    wbr
    cc0
    cA
    cN
    cexp
    co
    cle
    wbr
    reexpcld.1
    reexpcld.2
    expge0d.3
    cA
    cN
    expge0
    syl3anc
end

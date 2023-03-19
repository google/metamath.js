include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "mulgt1.mm"
include "syl22anc.mm"

theorem mulgt1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume divgt0d.2: |- ( ph -> B e. RR )
  assume mulgt1d.3: |- ( ph -> 1 < A )
  assume mulgt1d.4: |- ( ph -> 1 < B )


  assert |- ( ph -> 1 < ( A x. B ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    c1
    cA
    clt
    wbr
    c1
    cB
    clt
    wbr
    c1
    cA
    cB
    cmul
    co
    clt
    wbr
    ltp1d.1
    divgt0d.2
    mulgt1d.3
    mulgt1d.4
    cA
    cB
    mulgt1
    syl22anc
end

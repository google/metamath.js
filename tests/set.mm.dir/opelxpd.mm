include "wcel.mm"
include "cop.mm"
include "cxp.mm"
include "opelxpi.mm"
include "syl2anc.mm"

theorem opelxpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelxpd.1: |- ( ph -> A e. C )
  assume opelxpd.2: |- ( ph -> B e. D )


  assert |- ( ph -> <. A , B >. e. ( C X. D ) )

  proof
    wph
    cA
    cC
    wcel
    cB
    cD
    wcel
    cA
    cB
    cop
    cC
    cD
    cxp
    wcel
    opelxpd.1
    opelxpd.2
    cA
    cB
    cC
    cD
    opelxpi
    syl2anc
end

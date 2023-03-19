include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "cxplea.mm"
include "syl221anc.mm"

theorem cxplead
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume cxplead.2: |- ( ph -> 1 <_ A )
  assume cxplead.3: |- ( ph -> B e. RR )
  assume cxplead.4: |- ( ph -> C e. RR )
  assume cxplead.5: |- ( ph -> B <_ C )


  assert |- ( ph -> ( A ^c B ) <_ ( A ^c C ) )

  proof
    wph
    cA
    cr
    wcel
    c1
    cA
    cle
    wbr
    cB
    cr
    wcel
    cC
    cr
    wcel
    cB
    cC
    cle
    wbr
    cA
    cB
    ccxp
    co
    cA
    cC
    ccxp
    co
    cle
    wbr
    recxpcld.1
    cxplead.2
    cxplead.3
    cxplead.4
    cxplead.5
    cA
    cB
    cC
    cxplea
    syl221anc
end

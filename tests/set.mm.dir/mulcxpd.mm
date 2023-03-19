include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "cmul.mm"
include "co.mm"
include "ccxp.mm"
include "wceq.mm"
include "mulcxp.mm"
include "syl221anc.mm"

theorem mulcxpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume recxpcld.2: |- ( ph -> 0 <_ A )
  assume recxpcld.3: |- ( ph -> B e. RR )
  assume mulcxpd.4: |- ( ph -> 0 <_ B )
  assume mulcxpd.5: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A x. B ) ^c C ) = ( ( A ^c C ) x. ( B ^c C ) ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cC
    cc
    wcel
    cA
    cB
    cmul
    co
    cC
    ccxp
    co
    cA
    cC
    ccxp
    co
    cB
    cC
    ccxp
    co
    cmul
    co
    wceq
    recxpcld.1
    recxpcld.2
    recxpcld.3
    mulcxpd.4
    mulcxpd.5
    cA
    cB
    cC
    mulcxp
    syl221anc
end

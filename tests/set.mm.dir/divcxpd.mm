include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "cc.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "wceq.mm"
include "divcxp.mm"
include "syl211anc.mm"

theorem divcxpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume recxpcld.1: |- ( ph -> A e. RR )
  assume recxpcld.2: |- ( ph -> 0 <_ A )
  assume divcxpd.4: |- ( ph -> B e. RR+ )
  assume divcxpd.5: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A / B ) ^c C ) = ( ( A ^c C ) / ( B ^c C ) ) )

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
    crp
    wcel
    cC
    cc
    wcel
    cA
    cB
    cdiv
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
    cdiv
    co
    wceq
    recxpcld.1
    recxpcld.2
    divcxpd.4
    divcxpd.5
    cA
    cB
    cC
    divcxp
    syl211anc
end

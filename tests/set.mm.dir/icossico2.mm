include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cico.mm"
include "co.mm"
include "wss.mm"
include "xrleidd.mm"
include "icossico.mm"
include "syl22anc.mm"

theorem icossico2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume icossico2.1: |- ( ph -> B e. RR* )
  assume icossico2.2: |- ( ph -> C e. RR* )
  assume icossico2.3: |- ( ph -> B <_ A )


  assert |- ( ph -> ( A [,) C ) C_ ( B [,) C ) )

  proof
    wph
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    cB
    cA
    cle
    wbr
    cC
    cC
    cle
    wbr
    cA
    cC
    cico
    co
    cB
    cC
    cico
    co
    wss
    icossico2.1
    icossico2.2
    icossico2.3
    wph
    cC
    icossico2.2
    xrleidd
    cB
    cC
    cA
    cC
    icossico
    syl22anc
end

include "cxr.mm"
include "wcel.mm"
include "cico.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "icoltub.mm"
include "syl3anc.mm"

theorem icoltubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume icoltubd.1: |- ( ph -> A e. RR* )
  assume icoltubd.2: |- ( ph -> B e. RR* )
  assume icoltubd.3: |- ( ph -> C e. ( A [,) B ) )


  assert |- ( ph -> C < B )

  proof
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cC
    cA
    cB
    cico
    co
    wcel
    cC
    cB
    clt
    wbr
    icoltubd.1
    icoltubd.2
    icoltubd.3
    cA
    cB
    cC
    icoltub
    syl3anc
end

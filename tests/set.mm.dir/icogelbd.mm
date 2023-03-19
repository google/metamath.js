include "cxr.mm"
include "wcel.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "icogelb.mm"
include "syl3anc.mm"

theorem icogelbd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume icogelbd.1: |- ( ph -> A e. RR* )
  assume icogelbd.2: |- ( ph -> B e. RR* )
  assume icogelbd.3: |- ( ph -> C e. ( A [,) B ) )


  assert |- ( ph -> A <_ C )

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
    cA
    cC
    cle
    wbr
    icogelbd.1
    icogelbd.2
    icogelbd.3
    cA
    cB
    cC
    icogelb
    syl3anc
end

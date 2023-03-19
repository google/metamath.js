include "cxr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "iccgelb.mm"
include "syl3anc.mm"

theorem iccgelbd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iccgelbd.1: |- ( ph -> A e. RR* )
  assume iccgelbd.2: |- ( ph -> B e. RR* )
  assume iccgelbd.3: |- ( ph -> C e. ( A [,] B ) )


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
    cicc
    co
    wcel
    cA
    cC
    cle
    wbr
    iccgelbd.1
    iccgelbd.2
    iccgelbd.3
    cA
    cB
    cC
    iccgelb
    syl3anc
end

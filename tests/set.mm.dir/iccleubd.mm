include "cxr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "iccleub.mm"
include "syl3anc.mm"

theorem iccleubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iccleubd.1: |- ( ph -> A e. RR* )
  assume iccleubd.2: |- ( ph -> B e. RR* )
  assume iccleubd.3: |- ( ph -> C e. ( A [,] B ) )


  assert |- ( ph -> C <_ B )

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
    cC
    cB
    cle
    wbr
    iccleubd.1
    iccleubd.2
    iccleubd.3
    cA
    cB
    cC
    iccleub
    syl3anc
end

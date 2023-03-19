include "cxr.mm"
include "wcel.mm"
include "cioc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "iocleub.mm"
include "syl3anc.mm"

theorem iocleubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iocleubd.1: |- ( ph -> A e. RR* )
  assume iocleubd.2: |- ( ph -> B e. RR* )
  assume iocleubd.3: |- ( ph -> C e. ( A (,] B ) )


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
    cioc
    co
    wcel
    cC
    cB
    cle
    wbr
    iocleubd.1
    iocleubd.2
    iocleubd.3
    cA
    cB
    cC
    iocleub
    syl3anc
end

include "cxr.mm"
include "wcel.mm"
include "cioc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "iocgtlb.mm"
include "syl3anc.mm"

theorem iocgtlbd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iocgtlbd.1: |- ( ph -> A e. RR* )
  assume iocgtlbd.2: |- ( ph -> B e. RR* )
  assume iocgtlbd.3: |- ( ph -> C e. ( A (,] B ) )


  assert |- ( ph -> A < C )

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
    cA
    cC
    clt
    wbr
    iocgtlbd.1
    iocgtlbd.2
    iocgtlbd.3
    cA
    cB
    cC
    iocgtlb
    syl3anc
end

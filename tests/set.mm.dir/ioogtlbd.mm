include "cxr.mm"
include "wcel.mm"
include "cioo.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"

theorem ioogtlbd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ioogtlbd.1: |- ( ph -> A e. RR* )
  assume ioogtlbd.2: |- ( ph -> B e. RR* )
  assume ioogtlbd.3: |- ( ph -> C e. ( A (,) B ) )


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
    cioo
    co
    wcel
    cA
    cC
    clt
    wbr
    ioogtlbd.1
    ioogtlbd.2
    ioogtlbd.3
    cA
    cB
    cC
    ioogtlb
    syl3anc
end

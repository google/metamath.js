include "cxr.mm"
include "wcel.mm"
include "cioo.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "iooltub.mm"
include "syl3anc.mm"

theorem iooltubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume iooltubd.1: |- ( ph -> A e. RR* )
  assume iooltubd.2: |- ( ph -> B e. RR* )
  assume iooltubd.3: |- ( ph -> C e. ( A (,) B ) )


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
    cioo
    co
    wcel
    cC
    cB
    clt
    wbr
    iooltubd.1
    iooltubd.2
    iooltubd.3
    cA
    cB
    cC
    iooltub
    syl3anc
end

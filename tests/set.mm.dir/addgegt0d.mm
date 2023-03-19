include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "caddc.mm"
include "co.mm"
include "addgegt0.mm"
include "syl22anc.mm"

theorem addgegt0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume addgegt0d.3: |- ( ph -> 0 <_ A )
  assume addgegt0d.4: |- ( ph -> 0 < B )


  assert |- ( ph -> 0 < ( A + B ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cc0
    cB
    clt
    wbr
    cc0
    cA
    cB
    caddc
    co
    clt
    wbr
    leidd.1
    ltnegd.2
    addgegt0d.3
    addgegt0d.4
    cA
    cB
    addgegt0
    syl22anc
end

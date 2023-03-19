include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "mulge0.mm"
include "syl22anc.mm"

theorem mulge0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume addge0d.3: |- ( ph -> 0 <_ A )
  assume addge0d.4: |- ( ph -> 0 <_ B )


  assert |- ( ph -> 0 <_ ( A x. B ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cc0
    cA
    cB
    cmul
    co
    cle
    wbr
    leidd.1
    addge0d.3
    ltnegd.2
    addge0d.4
    cA
    cB
    mulge0
    syl22anc
end

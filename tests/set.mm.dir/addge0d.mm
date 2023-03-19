include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "addge0.mm"
include "syl22anc.mm"

theorem addge0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume addge0d.3: |- ( ph -> 0 <_ A )
  assume addge0d.4: |- ( ph -> 0 <_ B )


  assert |- ( ph -> 0 <_ ( A + B ) )

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
    cle
    wbr
    cc0
    cA
    cB
    caddc
    co
    cle
    wbr
    leidd.1
    ltnegd.2
    addge0d.3
    addge0d.4
    cA
    cB
    addge0
    syl22anc
end

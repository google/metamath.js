include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "caddc.mm"
include "co.mm"
include "addgtge0.mm"
include "syl22anc.mm"

theorem addgtge0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume addgtge0d.1: |- ( ph -> A e. RR )
  assume addgtge0d.2: |- ( ph -> B e. RR )
  assume addgtge0d.3: |- ( ph -> 0 < A )
  assume addgtge0d.4: |- ( ph -> 0 <_ B )


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
    clt
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
    clt
    wbr
    addgtge0d.1
    addgtge0d.2
    addgtge0d.3
    addgtge0d.4
    cA
    cB
    addgtge0
    syl22anc
end

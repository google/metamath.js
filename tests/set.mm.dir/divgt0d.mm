include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "divgt0.mm"
include "syl22anc.mm"

theorem divgt0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume divgt0d.2: |- ( ph -> B e. RR )
  assume divgt0d.3: |- ( ph -> 0 < A )
  assume divgt0d.4: |- ( ph -> 0 < B )


  assert |- ( ph -> 0 < ( A / B ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    cc0
    cA
    cB
    cdiv
    co
    clt
    wbr
    ltp1d.1
    divgt0d.3
    divgt0d.2
    divgt0d.4
    cA
    cB
    divgt0
    syl22anc
end

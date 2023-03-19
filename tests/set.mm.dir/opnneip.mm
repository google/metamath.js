include "wcel.mm"
include "ctop.mm"
include "csn.mm"
include "wss.mm"
include "cnei.mm"
include "cfv.mm"
include "snssi.mm"
include "opnneiss.mm"
include "syl3an3.mm"

theorem opnneip
  let cP: class P
  let cJ: class J
  let cN: class N


  assert |- ( ( J e. Top /\ N e. J /\ P e. N ) -> N e. ( ( nei ` J ) ` { P } ) )

  proof
    cP
    cN
    wcel
    cJ
    ctop
    wcel
    cN
    cJ
    wcel
    cP
    csn
    #
    cN
    wss
    cN
    @0
    cJ
    cnei
    cfv
    cfv
    wcel
    cP
    cN
    snssi
    @0
    cJ
    cN
    opnneiss
    syl3an3
end

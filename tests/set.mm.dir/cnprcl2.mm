include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnp.mm"
include "co.mm"
include "wa.mm"
include "cuni.mm"
include "eqid.mm"
include "cnprcl.mm"
include "adantl.mm"
include "wceq.mm"
include "toponuni.mm"
include "adantr.mm"
include "eleqtrrd.mm"

theorem cnprcl2
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let cY: class Y


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( ( J CnP K ) ` P ) ) -> P e. X )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    wa
    cP
    cJ
    cuni
    #
    cX
    @1
    cP
    @2
    wcel
    @0
    cP
    cF
    cJ
    cK
    @2
    @2
    eqid
    cnprcl
    adantl
    @0
    cX
    @2
    wceq
    @1
    cX
    cJ
    toponuni
    adantr
    eleqtrrd
end

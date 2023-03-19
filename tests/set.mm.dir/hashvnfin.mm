include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "cfn.mm"
include "wi.mm"
include "eleq1a.mm"
include "adantl.mm"
include "wb.mm"
include "hashclb.mm"
include "bicomd.mm"
include "adantr.mm"
include "sylibd.mm"

theorem hashvnfin
  let cS: class S
  let cN: class N
  let cV: class V


  assert |- ( ( S e. V /\ N e. NN0 ) -> ( ( # ` S ) = N -> S e. Fin ) )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    cS
    chash
    cfv
    #
    cN
    wceq
    #
    @2
    cn0
    wcel
    #
    cS
    cfn
    wcel
    #
    @1
    @3
    @4
    wi
    @0
    cN
    cn0
    @2
    eleq1a
    adantl
    @0
    @4
    @5
    wb
    @1
    @0
    @5
    @4
    cS
    cV
    hashclb
    bicomd
    adantr
    sylibd
end

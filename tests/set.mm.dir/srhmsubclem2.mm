include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "cin.mm"
include "cringc.mm"
include "cfv.mm"
include "cbs.mm"
include "srhmsubclem1.mm"
include "adantl.mm"
include "wceq.mm"
include "eqid.mm"
include "id.mm"
include "ringcbas.mm"
include "adantr.mm"
include "eleqtrrd.mm"

theorem srhmsubclem2
  let cC: class C
  let cS: class S
  let cU: class U
  let cV: class V
  let cX: class X
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume srhmsubc.s: |- A. r e. S r e. Ring
  assume srhmsubc.c: |- C = ( U i^i S )

  disjoint S r
  disjoint X r
  disjoint k x
  assert |- ( ( U e. V /\ X e. C ) -> X e. ( Base ` ( RingCat ` U ) ) )

  proof
    cU
    cV
    wcel
    #
    cX
    cC
    wcel
    #
    wa
    cX
    cU
    crg
    cin
    #
    cU
    cringc
    cfv
    #
    cbs
    cfv
    #
    @1
    cX
    @2
    wcel
    @0
    cC
    cS
    cU
    cX
    vr
    srhmsubc.s
    srhmsubc.c
    srhmsubclem1
    adantl
    @0
    @4
    @2
    wceq
    @1
    @0
    @4
    @3
    cU
    cV
    @3
    eqid
    @4
    eqid
    @0
    id
    ringcbas
    adantr
    eleqtrrd
end

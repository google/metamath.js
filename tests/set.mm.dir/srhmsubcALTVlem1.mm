include "wcel.mm"
include "wa.mm"
include "crg.mm"
include "cin.mm"
include "cringcALTV.mm"
include "cfv.mm"
include "cbs.mm"
include "srhmsubclem1.mm"
include "adantl.mm"
include "wceq.mm"
include "eqid.mm"
include "id.mm"
include "ringcbasALTV.mm"
include "adantr.mm"
include "eleqtrrd.mm"

theorem srhmsubcALTVlem1
  let cC: class C
  let cS: class S
  let cU: class U
  let cV: class V
  let cX: class X
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x
  assume srhmsubcALTV.s: |- A. r e. S r e. Ring
  assume srhmsubcALTV.c: |- C = ( U i^i S )

  disjoint S r
  disjoint X r
  disjoint k x
  assert |- ( ( U e. V /\ X e. C ) -> X e. ( Base ` ( RingCatALTV ` U ) ) )

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
    cringcALTV
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
    srhmsubcALTV.s
    srhmsubcALTV.c
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
    ringcbasALTV
    adantr
    eleqtrrd
end

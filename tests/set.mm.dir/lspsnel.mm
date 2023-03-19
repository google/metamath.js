include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "lspsn.mm"
include "eleq2d.mm"
include "cvv.mm"
include "id.mm"
include "ovex.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem lspsnel
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vv: setvar v
  let cR: class R
  assume lspsn.f: |- F = ( Scalar ` W )
  assume lspsn.k: |- K = ( Base ` F )
  assume lspsn.v: |- V = ( Base ` W )
  assume lspsn.t: |- .x. = ( .s ` W )
  assume lspsn.n: |- N = ( LSpan ` W )

  disjoint F k
  disjoint K k
  disjoint N k
  disjoint U k
  disjoint V k
  disjoint W k
  disjoint .x. k
  disjoint X k
  disjoint k v
  disjoint K v
  disjoint N v
  disjoint U v
  disjoint V v
  disjoint W v
  disjoint R k
  disjoint .x. v
  disjoint X v
  assert |- ( ( W e. LMod /\ X e. V ) -> ( U e. ( N ` { X } ) <-> E. k e. K U = ( k .x. X ) ) )

  proof
    cW
    clmod
    wcel
    cX
    cV
    wcel
    wa
    #
    cU
    cX
    csn
    cN
    cfv
    #
    wcel
    cU
    vv
    cv
    #
    vk
    cv
    #
    cX
    c.x
    co
    #
    wceq
    #
    vk
    cK
    wrex
    #
    vv
    cab
    #
    wcel
    cU
    @4
    wceq
    #
    vk
    cK
    wrex
    #
    @0
    @1
    @7
    cU
    vv
    c.x
    vk
    cF
    cK
    cN
    cV
    cW
    cX
    lspsn.f
    lspsn.k
    lspsn.v
    lspsn.t
    lspsn.n
    lspsn
    eleq2d
    @6
    @9
    vv
    cU
    @8
    cU
    cvv
    wcel
    vk
    cK
    @8
    cU
    @4
    cvv
    @8
    id
    @3
    cX
    c.x
    ovex
    syl6eqel
    rexlimivw
    @2
    cU
    wceq
    @5
    @8
    vk
    cK
    @2
    cU
    @4
    eqeq1
    rexbidv
    elab3
    syl6bb
end

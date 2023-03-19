include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "clss.mm"
include "cfv.mm"
include "csn.mm"
include "co.mm"
include "eqid.mm"
include "simp1.mm"
include "wss.mm"
include "simp3.mm"
include "snssd.mm"
include "lspcl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "lspsneli.mm"
include "lspsnel5a.mm"

theorem lspsnvsi
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vv: setvar v
  let cU: class U
  assume lspsn.f: |- F = ( Scalar ` W )
  assume lspsn.k: |- K = ( Base ` F )
  assume lspsn.v: |- V = ( Base ` W )
  assume lspsn.t: |- .x. = ( .s ` W )
  assume lspsn.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ R e. K /\ X e. V ) -> ( N ` { ( R .x. X ) } ) C_ ( N ` { X } ) )

  proof
    cW
    clmod
    wcel
    #
    cR
    cK
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cW
    clss
    cfv
    #
    cX
    csn
    #
    cN
    cfv
    #
    cN
    cW
    cR
    cX
    c.x
    co
    @4
    eqid
    #
    lspsn.n
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    @5
    cV
    wss
    @6
    @4
    wcel
    @8
    @3
    cX
    cV
    @0
    @1
    @2
    simp3
    #
    snssd
    @4
    @5
    cN
    cV
    cW
    lspsn.v
    @7
    lspsn.n
    lspcl
    syl2anc
    @3
    cR
    c.x
    cF
    cK
    cN
    cV
    cW
    cX
    lspsn.v
    lspsn.t
    lspsn.f
    lspsn.k
    lspsn.n
    @8
    @0
    @1
    @2
    simp2
    @9
    lspsneli
    lspsnel5a
end

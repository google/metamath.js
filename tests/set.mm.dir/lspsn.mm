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
include "clss.mm"
include "eqid.mm"
include "simpl.mm"
include "lss1d.mm"
include "cur.mm"
include "lmod1cl.mm"
include "adantr.mm"
include "lmodvs1.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elabg.mm"
include "adantl.mm"
include "mpbird.mm"
include "lspsnel5a.mm"
include "wi.mm"
include "lspsncl.mm"
include "simpr.mm"
include "lspsnid.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "eqssd.mm"

theorem lspsn
  let vv: setvar v
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cU: class U
  let cR: class R
  assume lspsn.f: |- F = ( Scalar ` W )
  assume lspsn.k: |- K = ( Base ` F )
  assume lspsn.v: |- V = ( Base ` W )
  assume lspsn.t: |- .x. = ( .s ` W )
  assume lspsn.n: |- N = ( LSpan ` W )

  disjoint F k
  disjoint k v
  disjoint K k
  disjoint K v
  disjoint N k
  disjoint N v
  disjoint V k
  disjoint V v
  disjoint W k
  disjoint W v
  disjoint .x. k
  disjoint .x. v
  disjoint X k
  disjoint X v
  disjoint U k
  disjoint U v
  disjoint R k
  assert |- ( ( W e. LMod /\ X e. V ) -> ( N ` { X } ) = { v | E. k e. K v = ( k .x. X ) } )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cX
    csn
    cN
    cfv
    #
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
    @2
    cW
    clss
    cfv
    #
    @9
    cN
    cW
    cX
    @10
    eqid
    #
    lspsn.n
    @0
    @1
    simpl
    #
    vv
    @10
    c.x
    vk
    cF
    cK
    cV
    cW
    cX
    lspsn.v
    lspsn.f
    lspsn.t
    lspsn.k
    @11
    lss1d
    @2
    cX
    @9
    wcel
    #
    cX
    @6
    wceq
    #
    vk
    cK
    wrex
    #
    @2
    cF
    cur
    cfv
    #
    cK
    wcel
    #
    cX
    @16
    cX
    c.x
    co
    #
    wceq
    #
    @15
    @0
    @17
    @1
    @16
    cF
    cK
    cW
    lspsn.f
    lspsn.k
    @16
    eqid
    #
    lmod1cl
    adantr
    @2
    @18
    cX
    c.x
    @16
    cF
    cV
    cW
    cX
    lspsn.v
    lspsn.f
    lspsn.t
    @20
    lmodvs1
    eqcomd
    @14
    @19
    vk
    @16
    cK
    @5
    @16
    wceq
    @6
    @18
    cX
    @5
    @16
    cX
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @1
    @13
    @15
    wb
    @0
    @8
    @15
    vv
    cX
    cV
    @4
    cX
    wceq
    @7
    @14
    vk
    cK
    @4
    cX
    @6
    eqeq1
    rexbidv
    elabg
    adantl
    mpbird
    lspsnel5a
    @2
    @8
    vv
    @3
    @2
    @7
    @4
    @3
    wcel
    #
    vk
    cK
    @2
    @5
    cK
    wcel
    #
    wa
    #
    @6
    @3
    wcel
    #
    @7
    @21
    wi
    @23
    @0
    @3
    @10
    wcel
    #
    @22
    cX
    @3
    wcel
    #
    @24
    @2
    @0
    @22
    @12
    adantr
    @2
    @25
    @22
    @10
    cN
    cV
    cW
    cX
    lspsn.v
    @11
    lspsn.n
    lspsncl
    adantr
    @2
    @22
    simpr
    @2
    @26
    @22
    cN
    cV
    cW
    cX
    lspsn.v
    lspsn.n
    lspsnid
    adantr
    cK
    @10
    c.x
    @3
    cF
    cW
    @5
    cX
    lspsn.f
    lspsn.t
    lspsn.k
    @11
    lssvscl
    syl22anc
    @6
    @3
    @4
    eleq1a
    syl
    rexlimdva
    abssdv
    eqssd
end

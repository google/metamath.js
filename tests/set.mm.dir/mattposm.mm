include "ccrg.mm"
include "wcel.mm"
include "w3a.mm"
include "cotp.mm"
include "cmmul.mm"
include "co.mm"
include "ctpos.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "simp1.mm"
include "cfn.mm"
include "cvv.mm"
include "matrcl.mm"
include "simpld.mm"
include "3ad2ant3.mm"
include "cxp.mm"
include "cmap.mm"
include "matbas2i.mm"
include "3ad2ant2.mm"
include "mamutpos.mm"
include "cmulr.mm"
include "wceq.mm"
include "matmulr.mm"
include "syl2anc.mm"
include "syl6reqr.mm"
include "oveqd.mm"
include "tposeqd.mm"
include "3eqtr4d.mm"

theorem mattposm
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cN: class N
  let cX: class X
  let cY: class Y
  assume mattposm.a: |- A = ( N Mat R )
  assume mattposm.b: |- B = ( Base ` A )
  assume mattposm.t: |- .x. = ( .r ` A )


  assert |- ( ( R e. CRing /\ X e. B /\ Y e. B ) -> tpos ( X .x. Y ) = ( tpos Y .x. tpos X ) )

  proof
    cR
    ccrg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    cR
    cN
    cN
    cN
    cotp
    cmmul
    co
    #
    co
    #
    ctpos
    cY
    ctpos
    #
    cX
    ctpos
    #
    @4
    co
    cX
    cY
    c.x
    co
    #
    ctpos
    @6
    @7
    c.x
    co
    @3
    cR
    cbs
    cfv
    #
    cN
    cR
    @4
    @4
    cN
    cN
    cX
    cY
    @4
    eqid
    #
    @10
    @9
    eqid
    #
    @0
    @1
    @2
    simp1
    #
    @2
    @0
    cN
    cfn
    wcel
    #
    @1
    @2
    @13
    cR
    cvv
    wcel
    cA
    cB
    cR
    cN
    cY
    mattposm.a
    mattposm.b
    matrcl
    simpld
    3ad2ant3
    #
    @14
    @14
    @1
    @0
    cX
    @9
    cN
    cN
    cxp
    cmap
    co
    #
    wcel
    @2
    cA
    cB
    cR
    @9
    cX
    cN
    mattposm.a
    @11
    mattposm.b
    matbas2i
    3ad2ant2
    @2
    @0
    cY
    @15
    wcel
    @1
    cA
    cB
    cR
    @9
    cY
    cN
    mattposm.a
    @11
    mattposm.b
    matbas2i
    3ad2ant3
    mamutpos
    @3
    @8
    @5
    @3
    c.x
    @4
    cX
    cY
    @3
    @4
    cA
    cmulr
    cfv
    #
    c.x
    @3
    @13
    @0
    @4
    @16
    wceq
    @14
    @12
    cA
    cR
    @4
    cN
    ccrg
    mattposm.a
    @10
    matmulr
    syl2anc
    mattposm.t
    syl6reqr
    #
    oveqd
    tposeqd
    @3
    c.x
    @4
    @6
    @7
    @17
    oveqd
    3eqtr4d
end

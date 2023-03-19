include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "cur.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "3ad2ant1.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqid.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simp2.mm"
include "simp3.mm"
include "lmodvsass.mm"
include "syl13anc.mm"
include "ringnegl.mm"
include "oveq1d.mm"
include "lmodvscl.mm"
include "lmodvneg1.mm"
include "3eqtr3d.mm"

theorem lmodvsinv
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume lmodvsinv.b: |- B = ( Base ` W )
  assume lmodvsinv.f: |- F = ( Scalar ` W )
  assume lmodvsinv.s: |- .x. = ( .s ` W )
  assume lmodvsinv.n: |- N = ( invg ` W )
  assume lmodvsinv.m: |- M = ( invg ` F )
  assume lmodvsinv.k: |- K = ( Base ` F )


  assert |- ( ( W e. LMod /\ R e. K /\ X e. B ) -> ( ( M ` R ) .x. X ) = ( N ` ( R .x. X ) ) )

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
    cB
    wcel
    #
    w3a
    #
    cF
    cur
    cfv
    #
    cM
    cfv
    #
    cR
    cF
    cmulr
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    @5
    cR
    cX
    c.x
    co
    #
    c.x
    co
    #
    cR
    cM
    cfv
    #
    cX
    c.x
    co
    @9
    cN
    cfv
    #
    @3
    @0
    @5
    cK
    wcel
    #
    @1
    @2
    @8
    @10
    wceq
    @0
    @1
    @2
    simp1
    #
    @3
    cF
    cgrp
    wcel
    #
    @4
    cK
    wcel
    #
    @13
    @3
    cF
    crg
    wcel
    #
    @15
    @0
    @1
    @17
    @2
    cF
    cW
    lmodvsinv.f
    lmodring
    3ad2ant1
    #
    cF
    ringgrp
    syl
    @3
    @17
    @16
    @18
    cK
    cF
    @4
    lmodvsinv.k
    @4
    eqid
    #
    ringidcl
    syl
    cK
    cF
    cM
    @4
    lmodvsinv.k
    lmodvsinv.m
    grpinvcl
    syl2anc
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    @5
    cR
    c.x
    @6
    cF
    cK
    cB
    cW
    cX
    lmodvsinv.b
    lmodvsinv.f
    lmodvsinv.s
    lmodvsinv.k
    @6
    eqid
    #
    lmodvsass
    syl13anc
    @3
    @7
    @11
    cX
    c.x
    @3
    cK
    cF
    @6
    @4
    cM
    cR
    lmodvsinv.k
    @21
    @19
    lmodvsinv.m
    @18
    @20
    ringnegl
    oveq1d
    @3
    @0
    @9
    cB
    wcel
    @10
    @12
    wceq
    @14
    cR
    c.x
    cF
    cK
    cB
    cW
    cX
    lmodvsinv.b
    lmodvsinv.f
    lmodvsinv.s
    lmodvsinv.k
    lmodvscl
    c.x
    @4
    cF
    cM
    cN
    cB
    cW
    @9
    lmodvsinv.b
    lmodvsinv.n
    lmodvsinv.f
    lmodvsinv.s
    @19
    lmodvsinv.m
    lmodvneg1
    syl2anc
    3eqtr3d
end

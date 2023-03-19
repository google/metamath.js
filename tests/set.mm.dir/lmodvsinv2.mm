include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cplusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "simp1.mm"
include "lmodgrp.mm"
include "syl.mm"
include "simp3.mm"
include "eqid.mm"
include "grprinv.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "simp2.mm"
include "grpinvcl.mm"
include "lmodvsdi.mm"
include "syl13anc.mm"
include "lmodvs0.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "grpinvid1.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem lmodvsinv2
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  assume lmodvsinv2.b: |- B = ( Base ` W )
  assume lmodvsinv2.f: |- F = ( Scalar ` W )
  assume lmodvsinv2.s: |- .x. = ( .s ` W )
  assume lmodvsinv2.n: |- N = ( invg ` W )
  assume lmodvsinv2.k: |- K = ( Base ` F )


  assert |- ( ( W e. LMod /\ R e. K /\ X e. B ) -> ( R .x. ( N ` X ) ) = ( N ` ( R .x. X ) ) )

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
    cR
    cX
    c.x
    co
    #
    cN
    cfv
    #
    cR
    cX
    cN
    cfv
    #
    c.x
    co
    #
    @3
    @5
    @7
    wceq
    #
    @4
    @7
    cW
    cplusg
    cfv
    #
    co
    #
    cW
    c0g
    cfv
    #
    wceq
    #
    @3
    cR
    cX
    @6
    @9
    co
    #
    c.x
    co
    #
    cR
    @11
    c.x
    co
    #
    @10
    @11
    @3
    @13
    @11
    cR
    c.x
    @3
    cW
    cgrp
    wcel
    #
    @2
    @13
    @11
    wceq
    @3
    @0
    @16
    @0
    @1
    @2
    simp1
    #
    cW
    lmodgrp
    syl
    #
    @0
    @1
    @2
    simp3
    #
    cB
    @9
    cW
    cN
    cX
    @11
    lmodvsinv2.b
    @9
    eqid
    #
    @11
    eqid
    #
    lmodvsinv2.n
    grprinv
    syl2anc
    oveq2d
    @3
    @0
    @1
    @2
    @6
    cB
    wcel
    #
    @14
    @10
    wceq
    @17
    @0
    @1
    @2
    simp2
    #
    @19
    @3
    @16
    @2
    @22
    @18
    @19
    cB
    cW
    cN
    cX
    lmodvsinv2.b
    lmodvsinv2.n
    grpinvcl
    syl2anc
    #
    @9
    cR
    c.x
    cF
    cK
    cB
    cW
    cX
    @6
    lmodvsinv2.b
    @20
    lmodvsinv2.f
    lmodvsinv2.s
    lmodvsinv2.k
    lmodvsdi
    syl13anc
    @3
    @0
    @1
    @15
    @11
    wceq
    @17
    @23
    c.x
    cF
    cK
    cW
    cR
    @11
    lmodvsinv2.f
    lmodvsinv2.s
    lmodvsinv2.k
    @21
    lmodvs0
    syl2anc
    3eqtr3d
    @3
    @16
    @4
    cB
    wcel
    @7
    cB
    wcel
    #
    @8
    @12
    wb
    @18
    cR
    c.x
    cF
    cK
    cB
    cW
    cX
    lmodvsinv2.b
    lmodvsinv2.f
    lmodvsinv2.s
    lmodvsinv2.k
    lmodvscl
    @3
    @0
    @1
    @22
    @25
    @17
    @23
    @24
    cR
    c.x
    cF
    cK
    cB
    cW
    @6
    lmodvsinv2.b
    lmodvsinv2.f
    lmodvsinv2.s
    lmodvsinv2.k
    lmodvscl
    syl3anc
    cB
    @9
    cW
    cN
    @4
    @7
    @11
    lmodvsinv2.b
    @20
    @21
    lmodvsinv2.n
    grpinvid1
    syl3anc
    mpbird
    eqcomd
end

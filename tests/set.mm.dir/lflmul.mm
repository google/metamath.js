include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "eqid.mm"
include "lmod0vcl.mm"
include "3ad2ant1.mm"
include "lfli.mm"
include "syl113anc.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmod0vrid.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "lfl0.mm"
include "3adant3.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "lflcl.mm"
include "3adant3l.mm"
include "lmodmcl.mm"
include "grprid.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"

theorem lflmul
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  assume lflmul.d: |- D = ( Scalar ` W )
  assume lflmul.k: |- K = ( Base ` D )
  assume lflmul.t: |- .X. = ( .r ` D )
  assume lflmul.v: |- V = ( Base ` W )
  assume lflmul.s: |- .x. = ( .s ` W )
  assume lflmul.f: |- F = ( LFnl ` W )


  assert |- ( ( W e. LMod /\ G e. F /\ ( R e. K /\ X e. V ) ) -> ( G ` ( R .x. X ) ) = ( R .X. ( G ` X ) ) )

  proof
    cW
    clmod
    wcel
    #
    cG
    cF
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
    wa
    #
    w3a
    #
    cR
    cX
    c.x
    co
    #
    cW
    c0g
    cfv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    cG
    cfv
    #
    cR
    cX
    cG
    cfv
    #
    c.xp
    co
    #
    @7
    cG
    cfv
    #
    cD
    cplusg
    cfv
    #
    co
    #
    @6
    cG
    cfv
    @12
    @5
    @0
    @1
    @2
    @3
    @7
    cV
    wcel
    #
    @10
    @15
    wceq
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @4
    simp2
    @0
    @1
    @2
    @3
    simp3l
    #
    @0
    @1
    @2
    @3
    simp3r
    #
    @0
    @1
    @16
    @4
    cV
    cW
    @7
    lflmul.v
    @7
    eqid
    #
    lmod0vcl
    3ad2ant1
    cD
    @8
    @14
    cR
    c.x
    c.xp
    cF
    cG
    cK
    cV
    cW
    cX
    @7
    clmod
    lflmul.v
    @8
    eqid
    #
    lflmul.d
    lflmul.s
    lflmul.k
    @14
    eqid
    #
    lflmul.t
    lflmul.f
    lfli
    syl113anc
    @5
    @9
    @6
    cG
    @5
    @0
    @6
    cV
    wcel
    #
    @9
    @6
    wceq
    @17
    @5
    @0
    @2
    @3
    @23
    @17
    @18
    @19
    cR
    c.x
    cD
    cK
    cV
    cW
    cX
    lflmul.v
    lflmul.d
    lflmul.s
    lflmul.k
    lmodvscl
    syl3anc
    @8
    cV
    cW
    @6
    @7
    lflmul.v
    @21
    @20
    lmod0vrid
    syl2anc
    fveq2d
    @5
    @15
    @12
    cD
    c0g
    cfv
    #
    @14
    co
    #
    @12
    @5
    @13
    @24
    @12
    @14
    @0
    @1
    @13
    @24
    wceq
    @4
    cD
    cF
    cG
    cW
    @24
    @7
    lflmul.d
    @24
    eqid
    #
    @20
    lflmul.f
    lfl0
    3adant3
    oveq2d
    @5
    cD
    cgrp
    wcel
    #
    @12
    cK
    wcel
    #
    @25
    @12
    wceq
    @0
    @1
    @27
    @4
    cD
    cW
    lflmul.d
    lmodfgrp
    3ad2ant1
    @5
    @0
    @2
    @11
    cK
    wcel
    #
    @28
    @17
    @18
    @0
    @1
    @3
    @29
    @2
    cD
    cF
    cG
    cK
    cV
    cW
    cX
    clmod
    lflmul.d
    lflmul.k
    lflmul.v
    lflmul.f
    lflcl
    3adant3l
    c.xp
    cD
    cK
    cW
    cR
    @11
    lflmul.d
    lflmul.k
    lflmul.t
    lmodmcl
    syl3anc
    cK
    @14
    cD
    @12
    @24
    lflmul.k
    @22
    @26
    grprid
    syl2anc
    eqtrd
    3eqtr3d
end

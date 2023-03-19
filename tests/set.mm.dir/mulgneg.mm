include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cn0.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cr.mm"
include "cn.mm"
include "wa.mm"
include "cc0.mm"
include "wo.mm"
include "elnn0.mm"
include "simpr.mm"
include "simpl3.mm"
include "mulgnegnn.mm"
include "syl2anc.mm"
include "c0g.mm"
include "simpl1.mm"
include "eqid.mm"
include "grpinvid.mm"
include "syl.mm"
include "oveq1d.mm"
include "mulg0.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "negeqd.mm"
include "neg0.mm"
include "syl6eq.mm"
include "3eqtr4rd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "simprr.mm"
include "nnzd.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "grpinvinv.mm"
include "simprl.mm"
include "recnd.mm"
include "negnegd.mm"
include "eqtr3d.mm"
include "simp2.mm"
include "elznn0nn.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem mulgneg
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mulgnncl.b: |- B = ( Base ` G )
  assume mulgnncl.t: |- .x. = ( .g ` G )
  assume mulgneg.i: |- I = ( invg ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( -u N .x. X ) = ( I ` ( N .x. X ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cN
    cn0
    wcel
    #
    cN
    cneg
    #
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    cI
    cfv
    #
    wceq
    #
    cN
    cr
    wcel
    #
    @5
    cn
    wcel
    #
    wa
    #
    @4
    @3
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    @9
    cN
    elnn0
    @3
    @13
    @9
    @14
    @3
    @13
    wa
    @13
    @2
    @9
    @3
    @13
    simpr
    @0
    @1
    @2
    @13
    simpl3
    cB
    c.x
    cG
    cI
    cN
    cX
    mulgnncl.b
    mulgnncl.t
    mulgneg.i
    mulgnegnn
    syl2anc
    @3
    @14
    wa
    #
    cG
    c0g
    cfv
    #
    cI
    cfv
    #
    @16
    @8
    @6
    @15
    @0
    @17
    @16
    wceq
    @0
    @1
    @2
    @14
    simpl1
    cG
    cI
    @16
    @16
    eqid
    #
    mulgneg.i
    grpinvid
    syl
    @15
    @7
    @16
    cI
    @15
    @7
    cc0
    cX
    c.x
    co
    #
    @16
    @15
    cN
    cc0
    cX
    c.x
    @3
    @14
    simpr
    #
    oveq1d
    @15
    @2
    @19
    @16
    wceq
    @0
    @1
    @2
    @14
    simpl3
    cB
    c.x
    cG
    cX
    @16
    mulgnncl.b
    @18
    mulgnncl.t
    mulg0
    syl
    #
    eqtrd
    fveq2d
    @15
    @6
    @19
    @16
    @15
    @5
    cc0
    cX
    c.x
    @15
    @5
    cc0
    cneg
    cc0
    @15
    cN
    cc0
    @20
    negeqd
    neg0
    syl6eq
    oveq1d
    @21
    eqtrd
    3eqtr4rd
    jaodan
    sylan2b
    @3
    @12
    wa
    #
    @6
    cI
    cfv
    #
    cI
    cfv
    #
    @6
    @8
    @22
    @0
    @6
    cB
    wcel
    #
    @24
    @6
    wceq
    @0
    @1
    @2
    @12
    simpl1
    #
    @22
    @0
    @5
    cz
    wcel
    @2
    @25
    @26
    @22
    @5
    @3
    @10
    @11
    simprr
    #
    nnzd
    @0
    @1
    @2
    @12
    simpl3
    #
    cB
    c.x
    cG
    @5
    cX
    mulgnncl.b
    mulgnncl.t
    mulgcl
    syl3anc
    cB
    cG
    cI
    @6
    mulgnncl.b
    mulgneg.i
    grpinvinv
    syl2anc
    @22
    @23
    @7
    cI
    @22
    @5
    cneg
    #
    cX
    c.x
    co
    #
    @23
    @7
    @22
    @11
    @2
    @30
    @23
    wceq
    @27
    @28
    cB
    c.x
    cG
    cI
    @5
    cX
    mulgnncl.b
    mulgnncl.t
    mulgneg.i
    mulgnegnn
    syl2anc
    @22
    @29
    cN
    cX
    c.x
    @22
    cN
    @22
    cN
    @3
    @10
    @11
    simprl
    recnd
    negnegd
    oveq1d
    eqtr3d
    fveq2d
    eqtr3d
    @3
    @1
    @4
    @12
    wo
    @0
    @1
    @2
    simp2
    cN
    elznn0nn
    sylib
    mpjaodan
end

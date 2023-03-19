include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "cplusg.mm"
include "wceq.mm"
include "cbs.mm"
include "simpl.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "adantr.mm"
include "eqid.mm"
include "lmod1cl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simpr.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmod0vrid.mm"
include "syldan.mm"
include "lmodvnegcl.mm"
include "lmodass.mm"
include "syl13anc.mm"
include "lmodvs1.mm"
include "oveq2d.mm"
include "grplinv.mm"
include "oveq1d.mm"
include "lmodvsdir.mm"
include "lmod0vs.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "lmodvnegid.mm"
include "lmod0vlid.mm"

theorem lmodvneg1
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lmodvneg1.v: |- V = ( Base ` W )
  assume lmodvneg1.n: |- N = ( invg ` W )
  assume lmodvneg1.f: |- F = ( Scalar ` W )
  assume lmodvneg1.s: |- .x. = ( .s ` W )
  assume lmodvneg1.u: |- .1. = ( 1r ` F )
  assume lmodvneg1.m: |- M = ( invg ` F )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( ( M ` .1. ) .x. X ) = ( N ` X ) )

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
    c.1
    cM
    cfv
    #
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
    @4
    cX
    cN
    cfv
    #
    @0
    @1
    @4
    cV
    wcel
    #
    @7
    @4
    wceq
    @2
    @0
    @3
    cF
    cbs
    cfv
    #
    wcel
    #
    @1
    @9
    @0
    @1
    simpl
    #
    @2
    cF
    cgrp
    wcel
    #
    c.1
    @10
    wcel
    #
    @11
    @0
    @13
    @1
    cF
    cW
    lmodvneg1.f
    lmodfgrp
    adantr
    #
    @0
    @14
    @1
    c.1
    cF
    @10
    cW
    lmodvneg1.f
    @10
    eqid
    #
    lmodvneg1.u
    lmod1cl
    adantr
    #
    @10
    cF
    cM
    c.1
    @16
    lmodvneg1.m
    grpinvcl
    syl2anc
    #
    @0
    @1
    simpr
    #
    @3
    c.x
    cF
    @10
    cV
    cW
    cX
    lmodvneg1.v
    lmodvneg1.f
    lmodvneg1.s
    @16
    lmodvscl
    syl3anc
    #
    @6
    cV
    cW
    @4
    @5
    lmodvneg1.v
    @6
    eqid
    #
    @5
    eqid
    #
    lmod0vrid
    syldan
    @2
    @4
    cX
    @8
    @6
    co
    #
    @6
    co
    #
    @5
    @8
    @6
    co
    #
    @7
    @8
    @2
    @4
    cX
    @6
    co
    #
    @8
    @6
    co
    #
    @24
    @25
    @2
    @0
    @9
    @1
    @8
    cV
    wcel
    #
    @27
    @24
    wceq
    @12
    @20
    @19
    cN
    cV
    cW
    cX
    lmodvneg1.v
    lmodvneg1.n
    lmodvnegcl
    #
    @6
    cV
    cW
    @4
    cX
    @8
    lmodvneg1.v
    @21
    lmodass
    syl13anc
    @2
    @26
    @5
    @8
    @6
    @2
    @4
    c.1
    cX
    c.x
    co
    #
    @6
    co
    #
    @26
    @5
    @2
    @30
    cX
    @4
    @6
    c.x
    c.1
    cF
    cV
    cW
    cX
    lmodvneg1.v
    lmodvneg1.f
    lmodvneg1.s
    lmodvneg1.u
    lmodvs1
    oveq2d
    @2
    @3
    c.1
    cF
    cplusg
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    cF
    c0g
    cfv
    #
    cX
    c.x
    co
    @31
    @5
    @2
    @33
    @35
    cX
    c.x
    @2
    @13
    @14
    @33
    @35
    wceq
    @15
    @17
    @10
    @32
    cF
    cM
    c.1
    @35
    @16
    @32
    eqid
    #
    @35
    eqid
    #
    lmodvneg1.m
    grplinv
    syl2anc
    oveq1d
    @2
    @0
    @11
    @14
    @1
    @34
    @31
    wceq
    @12
    @18
    @17
    @19
    @6
    @32
    @3
    c.1
    c.x
    cF
    @10
    cV
    cW
    cX
    lmodvneg1.v
    @21
    lmodvneg1.f
    lmodvneg1.s
    @16
    @36
    lmodvsdir
    syl13anc
    c.x
    cF
    @35
    cV
    cW
    cX
    @5
    lmodvneg1.v
    lmodvneg1.f
    lmodvneg1.s
    @37
    @22
    lmod0vs
    3eqtr3d
    eqtr3d
    oveq1d
    eqtr3d
    @2
    @23
    @5
    @4
    @6
    @6
    cN
    cV
    cW
    cX
    @5
    lmodvneg1.v
    @21
    @22
    lmodvneg1.n
    lmodvnegid
    oveq2d
    @0
    @1
    @28
    @25
    @8
    wceq
    @29
    @6
    cV
    cW
    @8
    @5
    lmodvneg1.v
    @21
    @22
    lmod0vlid
    syldan
    3eqtr3d
    eqtr3d
end

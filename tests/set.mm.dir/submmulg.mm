include "csubmnd.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cn.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cplusg.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "simpl1.mm"
include "eqid.mm"
include "ressplusg.mm"
include "syl.mm"
include "seqeq2d.mm"
include "fveq1d.mm"
include "cbs.mm"
include "simpr.mm"
include "wss.mm"
include "submss.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "sseldd.mm"
include "adantr.mm"
include "mulgnn.mm"
include "syl2anc.mm"
include "submbas.mm"
include "eleqtrd.mm"
include "3eqtr4d.mm"
include "c0g.mm"
include "subm0.mm"
include "mulg0.mm"
include "oveq1d.mm"
include "wo.mm"
include "simp2.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem submmulg
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume submmulgcl.t: |- .xb = ( .g ` G )
  assume submmulg.h: |- H = ( G |`s S )
  assume submmulg.t: |- .x. = ( .g ` H )


  assert |- ( ( S e. ( SubMnd ` G ) /\ N e. NN0 /\ X e. S ) -> ( N .xb X ) = ( N .x. X ) )

  proof
    cS
    cG
    csubmnd
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cN
    cn
    wcel
    #
    cN
    cX
    c.xb
    co
    #
    cN
    cX
    c.x
    co
    #
    wceq
    cN
    cc0
    wceq
    #
    @4
    @5
    wa
    #
    cN
    cG
    cplusg
    cfv
    #
    cn
    cX
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cN
    cH
    cplusg
    cfv
    #
    @11
    c1
    cseq
    #
    cfv
    #
    @6
    @7
    @9
    cN
    @12
    @15
    @9
    @10
    @14
    @11
    c1
    @9
    @1
    @10
    @14
    wceq
    @1
    @2
    @3
    @5
    simpl1
    cS
    @10
    cG
    cH
    @0
    submmulg.h
    @10
    eqid
    #
    ressplusg
    syl
    seqeq2d
    fveq1d
    @9
    @5
    cX
    cG
    cbs
    cfv
    #
    wcel
    #
    @6
    @13
    wceq
    @4
    @5
    simpr
    #
    @4
    @19
    @5
    @4
    cS
    @18
    cX
    @1
    @2
    cS
    @18
    wss
    @3
    @18
    cS
    cG
    @18
    eqid
    #
    submss
    3ad2ant1
    @1
    @2
    @3
    simp3
    #
    sseldd
    #
    adantr
    @18
    @10
    @12
    c.xb
    cG
    cN
    cX
    @21
    @17
    submmulgcl.t
    @12
    eqid
    mulgnn
    syl2anc
    @9
    @5
    cX
    cH
    cbs
    cfv
    #
    wcel
    #
    @7
    @16
    wceq
    @20
    @4
    @25
    @5
    @4
    cX
    cS
    @24
    @22
    @1
    @2
    cS
    @24
    wceq
    @3
    cS
    cH
    cG
    submmulg.h
    submbas
    3ad2ant1
    eleqtrd
    #
    adantr
    @24
    @14
    @15
    c.x
    cH
    cN
    cX
    @24
    eqid
    #
    @14
    eqid
    submmulg.t
    @15
    eqid
    mulgnn
    syl2anc
    3eqtr4d
    @4
    @8
    wa
    #
    cc0
    cX
    c.xb
    co
    #
    cc0
    cX
    c.x
    co
    #
    @6
    @7
    @28
    cG
    c0g
    cfv
    #
    cH
    c0g
    cfv
    #
    @29
    @30
    @28
    @1
    @31
    @32
    wceq
    @1
    @2
    @3
    @8
    simpl1
    cS
    cH
    cG
    @31
    submmulg.h
    @31
    eqid
    #
    subm0
    syl
    @28
    @19
    @29
    @31
    wceq
    @4
    @19
    @8
    @23
    adantr
    @18
    c.xb
    cG
    cX
    @31
    @21
    @33
    submmulgcl.t
    mulg0
    syl
    @28
    @25
    @30
    @32
    wceq
    @4
    @25
    @8
    @26
    adantr
    @24
    c.x
    cH
    cX
    @32
    @27
    @32
    eqid
    submmulg.t
    mulg0
    syl
    3eqtr4d
    @28
    cN
    cc0
    cX
    c.xb
    @4
    @8
    simpr
    #
    oveq1d
    @28
    cN
    cc0
    cX
    c.x
    @34
    oveq1d
    3eqtr4d
    @4
    @2
    @5
    @8
    wo
    @1
    @2
    @3
    simp2
    cN
    elnn0
    sylib
    mpjaodan
end

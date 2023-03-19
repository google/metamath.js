include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "simpl.mm"
include "crg.mm"
include "lmodring.mm"
include "adantr.mm"
include "eqid.mm"
include "ring0cl.mm"
include "syl.mm"
include "simpr.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grplid.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "wb.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmod0vid.mm"
include "syldan.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem lmod0vs
  let c.x: class .x.
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lmod0vs.v: |- V = ( Base ` W )
  assume lmod0vs.f: |- F = ( Scalar ` W )
  assume lmod0vs.s: |- .x. = ( .s ` W )
  assume lmod0vs.o: |- O = ( 0g ` F )
  assume lmod0vs.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( O .x. X ) = .0. )

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
    c.0
    cO
    cX
    c.x
    co
    #
    @2
    @3
    @3
    cW
    cplusg
    cfv
    #
    co
    #
    @3
    wceq
    #
    c.0
    @3
    wceq
    #
    @2
    cO
    cO
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
    @5
    @3
    @2
    @0
    cO
    cF
    cbs
    cfv
    #
    wcel
    #
    @12
    @1
    @10
    @5
    wceq
    @0
    @1
    simpl
    #
    @2
    cF
    crg
    wcel
    #
    @12
    @0
    @14
    @1
    cF
    cW
    lmod0vs.f
    lmodring
    adantr
    #
    @11
    cF
    cO
    @11
    eqid
    #
    lmod0vs.o
    ring0cl
    syl
    #
    @17
    @0
    @1
    simpr
    #
    @4
    @8
    cO
    cO
    c.x
    cF
    @11
    cV
    cW
    cX
    lmod0vs.v
    @4
    eqid
    #
    lmod0vs.f
    lmod0vs.s
    @16
    @8
    eqid
    #
    lmodvsdir
    syl13anc
    @2
    @9
    cO
    cX
    c.x
    @2
    cF
    cgrp
    wcel
    #
    @12
    @9
    cO
    wceq
    @2
    @14
    @21
    @15
    cF
    ringgrp
    syl
    @17
    @11
    @8
    cF
    cO
    cO
    @16
    @20
    lmod0vs.o
    grplid
    syl2anc
    oveq1d
    eqtr3d
    @0
    @1
    @3
    cV
    wcel
    #
    @6
    @7
    wb
    @2
    @0
    @12
    @1
    @22
    @13
    @17
    @18
    cO
    c.x
    cF
    @11
    cV
    cW
    cX
    lmod0vs.v
    lmod0vs.f
    lmod0vs.s
    @16
    lmodvscl
    syl3anc
    @4
    cV
    cW
    @3
    c.0
    lmod0vs.v
    @19
    lmod0vs.z
    lmod0vid
    syldan
    mpbid
    eqcomd
end

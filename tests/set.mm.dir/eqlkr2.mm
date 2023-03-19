include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "wrex.mm"
include "wral.mm"
include "eqlkr.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wf.mm"
include "wfn.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "lflf.mm"
include "syl2anc.mm"
include "ffn.mm"
include "syl.mm"
include "vex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "simpl2r.mm"
include "eqidd.mm"
include "fvconst2.mm"
include "adantl.mm"
include "offveqb.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem eqlkr2
  let cD: class D
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vx: setvar x
  let vz: setvar z
  assume eqlkr.d: |- D = ( Scalar ` W )
  assume eqlkr.k: |- K = ( Base ` D )
  assume eqlkr.t: |- .x. = ( .r ` D )
  assume eqlkr.v: |- V = ( Base ` W )
  assume eqlkr.f: |- F = ( LFnl ` W )
  assume eqlkr.l: |- L = ( LKer ` W )

  disjoint D r
  disjoint G r
  disjoint H r
  disjoint V r
  disjoint K r
  disjoint .x. r
  disjoint F r
  disjoint L r
  disjoint W r
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint F x
  disjoint F z
  disjoint G x
  disjoint G z
  disjoint H x
  disjoint H z
  disjoint V x
  disjoint V z
  disjoint K z
  disjoint L x
  disjoint L z
  disjoint .x. z
  disjoint W x
  disjoint W z
  disjoint K x
  disjoint .x. x
  assert |- ( ( W e. LVec /\ ( G e. F /\ H e. F ) /\ ( L ` G ) = ( L ` H ) ) -> E. r e. K H = ( G oF .x. ( V X. { r } ) ) )

  proof
    cW
    clvec
    wcel
    #
    cG
    cF
    wcel
    #
    cH
    cF
    wcel
    #
    wa
    #
    cG
    cL
    cfv
    cH
    cL
    cfv
    wceq
    #
    w3a
    #
    cH
    cG
    cV
    vr
    cv
    #
    csn
    cxp
    #
    c.x
    cof
    co
    wceq
    #
    vr
    cK
    wrex
    vx
    cv
    #
    cH
    cfv
    @9
    cG
    cfv
    #
    @6
    c.x
    co
    wceq
    vx
    cV
    wral
    #
    vr
    cK
    wrex
    vx
    cD
    c.x
    cF
    cG
    cH
    cK
    cL
    cV
    cW
    vr
    eqlkr.d
    eqlkr.k
    eqlkr.t
    eqlkr.v
    eqlkr.f
    eqlkr.l
    eqlkr
    @5
    @8
    @11
    vr
    cK
    @5
    @6
    cK
    wcel
    #
    wa
    #
    vx
    cV
    @10
    @6
    c.x
    cG
    @7
    cH
    cvv
    cV
    cvv
    wcel
    @13
    cV
    cW
    cbs
    cfv
    cvv
    eqlkr.v
    cW
    cbs
    fvex
    eqeltri
    a1i
    @13
    cV
    cK
    cG
    wf
    #
    cG
    cV
    wfn
    @13
    @0
    @1
    @14
    @0
    @3
    @4
    @12
    simpl1
    #
    @1
    @2
    @0
    @4
    @12
    simpl2l
    cD
    cF
    cG
    cK
    cV
    cW
    clvec
    eqlkr.d
    eqlkr.k
    eqlkr.v
    eqlkr.f
    lflf
    syl2anc
    cV
    cK
    cG
    ffn
    syl
    @6
    cvv
    wcel
    @7
    cV
    wfn
    @13
    vr
    vex
    #
    cV
    @6
    cvv
    fnconstg
    mp1i
    @13
    cV
    cK
    cH
    wf
    #
    cH
    cV
    wfn
    @13
    @0
    @2
    @17
    @15
    @1
    @2
    @0
    @4
    @12
    simpl2r
    cD
    cF
    cH
    cK
    cV
    cW
    clvec
    eqlkr.d
    eqlkr.k
    eqlkr.v
    eqlkr.f
    lflf
    syl2anc
    cV
    cK
    cH
    ffn
    syl
    @13
    @9
    cV
    wcel
    #
    wa
    @10
    eqidd
    @18
    @9
    @7
    cfv
    @6
    wceq
    @13
    cV
    @6
    @9
    @16
    fvconst2
    adantl
    offveqb
    rexbidva
    mpbird
end

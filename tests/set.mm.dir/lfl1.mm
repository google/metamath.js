include "clvec.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wral.mm"
include "nne.mm"
include "ralbii.mm"
include "wf.mm"
include "wfn.mm"
include "wi.mm"
include "cbs.mm"
include "eqid.mm"
include "lflf.mm"
include "ffn.mm"
include "syl.mm"
include "fconstfv.mm"
include "simplbi2.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fconst2.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "necon3ad.mm"
include "dfrex2.mm"
include "syl6ibr.mm"
include "3impia.mm"
include "cinvr.mm"
include "cvsca.mm"
include "co.mm"
include "clmod.mm"
include "simp1l.mm"
include "lveclmod.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "simp1r.mm"
include "simp2.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "simp3.mm"
include "drnginvrcl.mm"
include "lmodvscl.mm"
include "cmulr.mm"
include "lflmul.mm"
include "syl112anc.mm"
include "drnginvrl.mm"
include "eqtrd.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdv3a.mm"
include "3adant3.mm"
include "mpd.mm"

theorem lfl1
  let vx: setvar x
  let cD: class D
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vz: setvar z
  assume lfl1.d: |- D = ( Scalar ` W )
  assume lfl1.o: |- .0. = ( 0g ` D )
  assume lfl1.u: |- .1. = ( 1r ` D )
  assume lfl1.v: |- V = ( Base ` W )
  assume lfl1.f: |- F = ( LFnl ` W )

  disjoint D x
  disjoint G x
  disjoint .1. x
  disjoint V x
  disjoint W x
  disjoint F z
  disjoint x z
  disjoint G z
  disjoint .1. z
  disjoint V z
  disjoint W z
  disjoint .0. z
  assert |- ( ( W e. LVec /\ G e. F /\ G =/= ( V X. { .0. } ) ) -> E. x e. V ( G ` x ) = .1. )

  proof
    cW
    clvec
    wcel
    #
    cG
    cF
    wcel
    #
    cG
    cV
    c.0
    csn
    #
    cxp
    #
    wne
    #
    w3a
    vz
    cv
    #
    cG
    cfv
    #
    c.0
    wne
    #
    vz
    cV
    wrex
    #
    vx
    cv
    #
    cG
    cfv
    #
    c.1
    wceq
    #
    vx
    cV
    wrex
    #
    @0
    @1
    @4
    @8
    @0
    @1
    wa
    #
    @4
    @7
    wn
    #
    vz
    cV
    wral
    #
    wn
    @8
    @13
    @15
    cG
    @3
    @15
    @6
    c.0
    wceq
    #
    vz
    cV
    wral
    #
    @13
    cG
    @3
    wceq
    #
    @14
    @16
    vz
    cV
    @6
    c.0
    nne
    ralbii
    @13
    @17
    cV
    @2
    cG
    wf
    #
    @18
    @13
    cG
    cV
    wfn
    #
    @17
    @19
    wi
    @13
    cV
    cD
    cbs
    cfv
    #
    cG
    wf
    @20
    cD
    cF
    cG
    @21
    cV
    cW
    clvec
    lfl1.d
    @21
    eqid
    #
    lfl1.v
    lfl1.f
    lflf
    cV
    @21
    cG
    ffn
    syl
    @19
    @20
    @17
    vz
    cV
    c.0
    cG
    fconstfv
    simplbi2
    syl
    cV
    c.0
    cG
    c.0
    cD
    c0g
    cfv
    cvv
    lfl1.o
    cD
    c0g
    fvex
    eqeltri
    fconst2
    syl6ib
    syl5bi
    necon3ad
    @7
    vz
    cV
    dfrex2
    syl6ibr
    3impia
    @0
    @1
    @8
    @12
    wi
    @4
    @13
    @7
    @12
    vz
    cV
    @13
    @5
    cV
    wcel
    #
    @7
    w3a
    #
    @6
    cD
    cinvr
    cfv
    #
    cfv
    #
    @5
    cW
    cvsca
    cfv
    #
    co
    #
    cV
    wcel
    #
    @28
    cG
    cfv
    #
    c.1
    wceq
    #
    @12
    @24
    cW
    clmod
    wcel
    #
    @26
    @21
    wcel
    #
    @23
    @29
    @24
    @0
    @32
    @0
    @1
    @23
    @7
    simp1l
    #
    cW
    lveclmod
    syl
    #
    @24
    cD
    cdr
    wcel
    #
    @6
    @21
    wcel
    #
    @7
    @33
    @24
    @0
    @36
    @34
    cD
    cW
    lfl1.d
    lvecdrng
    syl
    #
    @24
    @0
    @1
    @23
    @37
    @34
    @0
    @1
    @23
    @7
    simp1r
    #
    @13
    @23
    @7
    simp2
    #
    cD
    cF
    cG
    @21
    cV
    cW
    @5
    clvec
    lfl1.d
    @22
    lfl1.v
    lfl1.f
    lflcl
    syl3anc
    #
    @13
    @23
    @7
    simp3
    #
    @21
    cD
    @25
    @6
    c.0
    @22
    lfl1.o
    @25
    eqid
    #
    drnginvrcl
    syl3anc
    #
    @40
    @26
    @27
    cD
    @21
    cV
    cW
    @5
    lfl1.v
    lfl1.d
    @27
    eqid
    #
    @22
    lmodvscl
    syl3anc
    @24
    @30
    @26
    @6
    cD
    cmulr
    cfv
    #
    co
    #
    c.1
    @24
    @32
    @1
    @33
    @23
    @30
    @47
    wceq
    @35
    @39
    @44
    @40
    cD
    @26
    @27
    @46
    cF
    cG
    @21
    cV
    cW
    @5
    lfl1.d
    @22
    @46
    eqid
    #
    lfl1.v
    @45
    lfl1.f
    lflmul
    syl112anc
    @24
    @36
    @37
    @7
    @47
    c.1
    wceq
    @38
    @41
    @42
    @21
    cD
    @46
    c.1
    @25
    @6
    c.0
    @22
    lfl1.o
    @48
    lfl1.u
    @43
    drnginvrl
    syl3anc
    eqtrd
    @11
    @31
    vx
    @28
    cV
    @9
    @28
    wceq
    @10
    @30
    c.1
    @9
    @28
    cG
    fveq2
    eqeq1d
    rspcev
    syl2anc
    rexlimdv3a
    3adant3
    mpd
end

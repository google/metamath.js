include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "cmap.mm"
include "wf.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmrsub.mm"
include "cop.mm"
include "cmpt.mm"
include "wa.mm"
include "cmtc.mm"
include "cxp.mm"
include "xp1st.mm"
include "eqid.mm"
include "mexval.mm"
include "eleq2s.mm"
include "adantl.mm"
include "mrsubff.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "syl.mm"
include "xp2nd.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "fmptd.mm"
include "cmex.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "sylibr.mm"
include "msubffval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem msubff
  let cR: class R
  let cS: class S
  let cT: class T
  let cE: class E
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  assume msubff.v: |- V = ( mVR ` T )
  assume msubff.r: |- R = ( mREx ` T )
  assume msubff.s: |- S = ( mSubst ` T )
  assume msubff.e: |- E = ( mEx ` T )


  assert |- ( T e. W -> S : ( R ^pm V ) --> ( E ^m E ) )

  proof
    cT
    cW
    wcel
    #
    cR
    cV
    cpm
    co
    #
    cE
    cE
    cmap
    co
    #
    cS
    wf
    @1
    @2
    vf
    @1
    ve
    cE
    ve
    cv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    vf
    cv
    #
    cT
    cmrsub
    cfv
    #
    cfv
    #
    cfv
    #
    cop
    #
    cmpt
    #
    cmpt
    #
    wf
    @0
    vf
    @1
    @11
    @2
    @12
    @0
    @6
    @1
    wcel
    wa
    #
    cE
    cE
    @11
    wf
    @11
    @2
    wcel
    @13
    ve
    cE
    @10
    cE
    @11
    @13
    @3
    cE
    wcel
    #
    wa
    #
    @10
    cT
    cmtc
    cfv
    #
    cR
    cxp
    #
    cE
    @15
    @4
    @16
    wcel
    #
    @9
    cR
    wcel
    #
    @10
    @17
    wcel
    @14
    @18
    @13
    @18
    @3
    @17
    cE
    @3
    @16
    cR
    xp1st
    cR
    cT
    cE
    @16
    @16
    eqid
    msubff.e
    msubff.r
    mexval
    #
    eleq2s
    adantl
    @13
    cR
    cR
    @8
    wf
    #
    @5
    cR
    wcel
    #
    @19
    @14
    @13
    @8
    cR
    cR
    cmap
    co
    #
    wcel
    @21
    @0
    @1
    @23
    @6
    @7
    cR
    @7
    cT
    cV
    cW
    msubff.v
    msubff.r
    @7
    eqid
    #
    mrsubff
    ffvelrnda
    @8
    cR
    cR
    elmapi
    syl
    @22
    @3
    @17
    cE
    @3
    @16
    cR
    xp2nd
    @20
    eleq2s
    cR
    cR
    @5
    @8
    ffvelrn
    syl2an
    @4
    @9
    @16
    cR
    opelxp
    sylanbrc
    @20
    syl6eleqr
    @11
    eqid
    fmptd
    cE
    cE
    @11
    cE
    cT
    cmex
    cfv
    cvv
    msubff.e
    cT
    cmex
    fvex
    eqeltri
    #
    @25
    elmap
    sylibr
    @12
    eqid
    fmptd
    @0
    @1
    @2
    cS
    @12
    cR
    cS
    cT
    ve
    vf
    cE
    @7
    cV
    cW
    msubff.v
    msubff.r
    msubff.s
    msubff.e
    @24
    msubffval
    feq1d
    mpbird
end

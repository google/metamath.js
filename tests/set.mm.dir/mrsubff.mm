include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "cmap.mm"
include "wf.mm"
include "cmcn.mm"
include "cfv.mm"
include "cun.mm"
include "cfrmd.mm"
include "cv.mm"
include "cdm.mm"
include "cs1.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cgsu.mm"
include "wa.mm"
include "cword.mm"
include "cmnd.mm"
include "cvv.mm"
include "fvex.mm"
include "cmvar.mm"
include "eqeltri.mm"
include "unex.mm"
include "eqid.mm"
include "frmdmnd.mm"
include "mp1i.mm"
include "simpr.mm"
include "wceq.mm"
include "mrexval.mm"
include "ad2antrr.mm"
include "eleqtrd.mm"
include "wss.mm"
include "elpmi.mm"
include "simpld.mm"
include "ad3antlr.mm"
include "ffvelrnda.mm"
include "wn.mm"
include "simplr.mm"
include "s1cld.mm"
include "ifclda.mm"
include "fmptd.mm"
include "wrdco.mm"
include "syl2anc.mm"
include "cbs.mm"
include "frmdbas.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "gsumwcl.mm"
include "eleqtrrd.mm"
include "cmrex.mm"
include "elmap.mm"
include "sylibr.mm"
include "mrsubffval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem mrsubff
  let cR: class R
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  assume mrsubvr.v: |- V = ( mVR ` T )
  assume mrsubvr.r: |- R = ( mREx ` T )
  assume mrsubvr.s: |- S = ( mRSubst ` T )


  assert |- ( T e. W -> S : ( R ^pm V ) --> ( R ^m R ) )

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
    cR
    cR
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
    cR
    cT
    cmcn
    cfv
    #
    cV
    cun
    #
    cfrmd
    cfv
    #
    vv
    @4
    vv
    cv
    #
    vf
    cv
    #
    cdm
    #
    wcel
    #
    @6
    @7
    cfv
    #
    @6
    cs1
    #
    cif
    #
    cmpt
    #
    ve
    cv
    #
    ccom
    #
    cgsu
    co
    #
    cmpt
    #
    cmpt
    #
    wf
    @0
    vf
    @1
    @17
    @2
    @18
    @0
    @7
    @1
    wcel
    #
    wa
    #
    cR
    cR
    @17
    wf
    @17
    @2
    wcel
    @20
    ve
    cR
    @16
    cR
    @17
    @20
    @14
    cR
    wcel
    #
    wa
    #
    @16
    @4
    cword
    #
    cR
    @22
    @5
    cmnd
    wcel
    #
    @15
    @23
    cword
    wcel
    #
    @16
    @23
    wcel
    @4
    cvv
    wcel
    #
    @24
    @22
    @3
    cV
    cT
    cmcn
    fvex
    cV
    cT
    cmvar
    cfv
    cvv
    mrsubvr.v
    cT
    cmvar
    fvex
    eqeltri
    unex
    #
    @4
    @5
    cvv
    @5
    eqid
    #
    frmdmnd
    mp1i
    @22
    @14
    @23
    wcel
    @4
    @23
    @13
    wf
    @25
    @22
    @14
    cR
    @23
    @20
    @21
    simpr
    @0
    cR
    @23
    wceq
    #
    @19
    @21
    @3
    cR
    cT
    cV
    cW
    @3
    eqid
    #
    mrsubvr.v
    mrsubvr.r
    mrexval
    ad2antrr
    #
    eleqtrd
    @22
    vv
    @4
    @12
    @23
    @13
    @22
    @6
    @4
    wcel
    #
    wa
    #
    @9
    @10
    @11
    @23
    @33
    @9
    wa
    @10
    cR
    @23
    @33
    @8
    cR
    @6
    @7
    @19
    @8
    cR
    @7
    wf
    #
    @0
    @21
    @32
    @19
    @34
    @8
    cV
    wss
    cR
    cV
    @7
    elpmi
    simpld
    ad3antlr
    ffvelrnda
    @22
    @29
    @32
    @9
    @31
    ad2antrr
    eleqtrd
    @33
    @9
    wn
    #
    wa
    @6
    @4
    @22
    @32
    @35
    simplr
    s1cld
    ifclda
    @13
    eqid
    fmptd
    @4
    @23
    @13
    @14
    wrdco
    syl2anc
    @23
    @5
    @15
    @5
    cbs
    cfv
    #
    @23
    @26
    @36
    @23
    wceq
    @27
    @36
    @4
    @5
    cvv
    @28
    @36
    eqid
    frmdbas
    ax-mp
    eqcomi
    gsumwcl
    syl2anc
    @31
    eleqtrrd
    @17
    eqid
    fmptd
    cR
    cR
    @17
    cR
    cT
    cmrex
    cfv
    cvv
    mrsubvr.r
    cT
    cmrex
    fvex
    eqeltri
    #
    @37
    elmap
    sylibr
    @18
    eqid
    fmptd
    @0
    @1
    @2
    cS
    @18
    vv
    @3
    cR
    cS
    cT
    ve
    vf
    @5
    cV
    cW
    @30
    mrsubvr.v
    mrsubvr.r
    mrsubvr.s
    @28
    mrsubffval
    feq1d
    mpbird
end

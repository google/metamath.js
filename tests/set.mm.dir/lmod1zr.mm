include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "ctp.mm"
include "cvsca.mm"
include "cv.mm"
include "cmpt2.mm"
include "cun.mm"
include "clmod.mm"
include "cxp.mm"
include "c2nd.mm"
include "cmpt.mm"
include "wf.mm"
include "wceq.mm"
include "elsni.mm"
include "fveq2.mm"
include "adantl.mm"
include "op2ndg.mm"
include "ancoms.mm"
include "snidg.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "sylan2.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "opex.mm"
include "simpl.mm"
include "fsng.mm"
include "sylancr.mm"
include "mpbid.mm"
include "xpsng.mm"
include "eqcomd.mm"
include "mpteq1d.mm"
include "eqtr3d.mm"
include "vex.mm"
include "op2ndd.mm"
include "mpt2mpt.mm"
include "a1i.mm"
include "snex.mm"
include "rngbase.mm"
include "mp1i.mm"
include "eqidd.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "opeq2d.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "crg.mm"
include "ring1.mm"
include "weq.mm"
include "id.mm"
include "cbvmpt2v.mm"
include "opeq2i.mm"
include "sneqi.mm"
include "uneq2i.mm"
include "lmod1.mm"

theorem lmod1zr
  let cR: class R
  let cI: class I
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vp: setvar p
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume lmod1zr.r: |- R = { <. ( Base ` ndx ) , { Z } >. , <. ( +g ` ndx ) , { <. <. Z , Z >. , Z >. } >. , <. ( .r ` ndx ) , { <. <. Z , Z >. , Z >. } >. }
  assume lmod1zr.m: |- M = ( { <. ( Base ` ndx ) , { I } >. , <. ( +g ` ndx ) , { <. <. I , I >. , I >. } >. , <. ( Scalar ` ndx ) , R >. } u. { <. ( .s ` ndx ) , { <. <. Z , I >. , I >. } >. } )


  assert |- ( ( I e. V /\ Z e. W ) -> M e. LMod )

  proof
    cI
    cV
    wcel
    #
    cZ
    cW
    wcel
    #
    wa
    #
    cM
    cnx
    cbs
    cfv
    cI
    csn
    #
    cop
    cnx
    cplusg
    cfv
    cI
    cI
    cop
    cI
    cop
    csn
    cop
    cnx
    csca
    cfv
    cR
    cop
    ctp
    #
    cnx
    cvsca
    cfv
    #
    vz
    vi
    cR
    cbs
    cfv
    #
    @3
    vi
    cv
    #
    cmpt2
    #
    cop
    #
    csn
    #
    cun
    #
    clmod
    @2
    cM
    @4
    @5
    cZ
    cI
    cop
    #
    cI
    cop
    csn
    #
    cop
    #
    csn
    #
    cun
    @11
    lmod1zr.m
    @2
    @15
    @10
    @4
    @2
    @14
    @9
    @2
    @13
    @8
    @5
    @2
    @13
    vp
    cZ
    csn
    #
    @3
    cxp
    #
    vp
    cv
    #
    c2nd
    cfv
    #
    cmpt
    #
    vz
    vi
    @16
    @3
    @7
    cmpt2
    #
    @8
    @2
    vp
    @12
    csn
    #
    @19
    cmpt
    #
    @13
    @20
    @2
    @22
    @3
    @23
    wf
    #
    @23
    @13
    wceq
    #
    @2
    vp
    @22
    @19
    @3
    @23
    @18
    @22
    wcel
    @2
    @18
    @12
    wceq
    #
    @19
    @3
    wcel
    @18
    @12
    elsni
    @2
    @26
    wa
    @19
    @12
    c2nd
    cfv
    #
    @3
    @26
    @19
    @27
    wceq
    @2
    @18
    @12
    c2nd
    fveq2
    adantl
    @2
    @27
    @3
    wcel
    @26
    @2
    @27
    cI
    @3
    @1
    @0
    @27
    cI
    wceq
    cZ
    cI
    cW
    cV
    op2ndg
    ancoms
    @0
    cI
    @3
    wcel
    @1
    cI
    cV
    snidg
    adantr
    eqeltrd
    adantr
    eqeltrd
    sylan2
    @23
    eqid
    fmptd
    @2
    @12
    cvv
    wcel
    @0
    @24
    @25
    wb
    cZ
    cI
    opex
    @0
    @1
    simpl
    @12
    cI
    cvv
    cV
    @23
    fsng
    sylancr
    mpbid
    @2
    vp
    @22
    @17
    @19
    @2
    @17
    @22
    @1
    @0
    @17
    @22
    wceq
    cZ
    cI
    cW
    cV
    xpsng
    ancoms
    eqcomd
    mpteq1d
    eqtr3d
    @20
    @21
    wceq
    @2
    vz
    vi
    vp
    @16
    @3
    @19
    @7
    vz
    cv
    @7
    @18
    vz
    vex
    vi
    vex
    op2ndd
    mpt2mpt
    a1i
    @2
    @16
    @6
    wceq
    #
    @3
    @3
    wceq
    @21
    @8
    wceq
    @16
    cvv
    wcel
    @28
    @2
    cZ
    snex
    @16
    cZ
    cZ
    cop
    cZ
    cop
    csn
    #
    cR
    @29
    cvv
    lmod1zr.r
    rngbase
    mp1i
    @2
    @3
    eqidd
    vz
    vi
    @16
    @3
    @6
    @3
    @7
    mpt2eq12
    syl2anc
    3eqtrd
    opeq2d
    sneqd
    uneq2d
    syl5eq
    @1
    @0
    cR
    crg
    wcel
    @11
    clmod
    wcel
    cR
    cW
    cZ
    lmod1zr.r
    ring1
    va
    vb
    cR
    cI
    @11
    cV
    @10
    @5
    va
    vb
    @6
    @3
    vb
    cv
    #
    cmpt2
    #
    cop
    #
    csn
    @4
    @9
    @32
    @8
    @31
    @5
    vz
    vi
    va
    vb
    @6
    @3
    @7
    @30
    @7
    vz
    va
    weq
    @7
    eqidd
    vi
    vb
    weq
    id
    cbvmpt2v
    opeq2i
    sneqi
    uneq2i
    lmod1
    sylan2
    eqeltrd
end

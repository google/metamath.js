include "caa.mm"
include "cq.mm"
include "citgo.mm"
include "cfv.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "wa.mm"
include "cply.mm"
include "wrex.mm"
include "cc.mm"
include "crab.mm"
include "wcel.mm"
include "rabid.mm"
include "wss.mm"
include "qsscn.mm"
include "itgoval.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "aacn.mm"
include "cmpaa.mm"
include "mpaacl.mm"
include "mpaaroot.mm"
include "cdgraa.mm"
include "mpaadgr.mm"
include "fveq2d.mm"
include "mpaamn.mm"
include "eqtrd.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "jca.mm"
include "c0p.mm"
include "csn.mm"
include "cdif.mm"
include "wne.mm"
include "simpl.mm"
include "cn0.mm"
include "cxp.mm"
include "coe0.mm"
include "fveq1i.mm"
include "dgr0.mm"
include "0nn0.mm"
include "eqeltri.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "eqtri.mm"
include "0ne1.mm"
include "eqnetri.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "necon2i.mm"
include "ad2antll.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "simprl.mm"
include "reximi2.mm"
include "anim2i.mm"
include "elqaa.mm"
include "sylibr.mm"
include "impbii.mm"
include "3bitr4ri.mm"
include "eqriv.mm"

theorem aaitgo
  let cS: class S
  let vx: setvar x
  let vp: setvar p
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cT: class T


  assert |- AA = ( IntgOver ` QQ )

  proof
    va
    caa
    cq
    citgo
    cfv
    #
    va
    cv
    #
    @1
    vb
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    @2
    cdgr
    cfv
    #
    @2
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    wa
    #
    vb
    cq
    cply
    cfv
    #
    wrex
    #
    va
    cc
    crab
    #
    wcel
    @1
    cc
    wcel
    #
    @11
    wa
    #
    @1
    @0
    wcel
    @1
    caa
    wcel
    #
    @11
    va
    cc
    rabid
    @0
    @12
    @1
    cq
    cc
    wss
    @0
    @12
    wceq
    qsscn
    va
    cq
    vb
    itgoval
    ax-mp
    eleq2i
    @15
    @14
    @15
    @13
    @11
    @1
    aacn
    @15
    @1
    cmpaa
    cfv
    #
    @10
    wcel
    @1
    @16
    cfv
    #
    cc0
    wceq
    #
    @16
    cdgr
    cfv
    #
    @16
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    #
    @11
    @1
    mpaacl
    @1
    mpaaroot
    @15
    @21
    @1
    cdgraa
    cfv
    #
    @20
    cfv
    c1
    @15
    @19
    @23
    @20
    @1
    mpaadgr
    fveq2d
    @1
    mpaamn
    eqtrd
    @9
    @18
    @22
    wa
    vb
    @16
    @10
    @2
    @16
    wceq
    #
    @4
    @18
    @8
    @22
    @24
    @3
    @17
    cc0
    @1
    @2
    @16
    fveq1
    eqeq1d
    @24
    @7
    @21
    c1
    @24
    @5
    @19
    @6
    @20
    @2
    @16
    ccoe
    fveq2
    @2
    @16
    cdgr
    fveq2
    fveq12d
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    jca
    @14
    @13
    @4
    vb
    @10
    c0p
    csn
    cdif
    #
    wrex
    #
    wa
    @15
    @11
    @26
    @13
    @9
    @4
    vb
    @10
    @25
    @2
    @10
    wcel
    #
    @9
    wa
    #
    @2
    @25
    wcel
    #
    @4
    @28
    @27
    @2
    c0p
    wne
    #
    @29
    @27
    @9
    simpl
    @8
    @30
    @27
    @4
    @2
    c0p
    @7
    c1
    @2
    c0p
    wceq
    #
    @7
    c1
    wne
    c0p
    cdgr
    cfv
    #
    c0p
    ccoe
    cfv
    #
    cfv
    #
    c1
    wne
    @34
    cc0
    c1
    @34
    @32
    cn0
    cc0
    csn
    cxp
    #
    cfv
    #
    cc0
    @32
    @33
    @35
    coe0
    fveq1i
    @32
    cn0
    wcel
    @36
    cc0
    wceq
    @32
    cc0
    cn0
    dgr0
    0nn0
    eqeltri
    cn0
    cc0
    @32
    c0ex
    fvconst2
    ax-mp
    eqtri
    0ne1
    eqnetri
    @31
    @7
    @34
    c1
    @31
    @5
    @32
    @6
    @33
    @2
    c0p
    ccoe
    fveq2
    @2
    c0p
    cdgr
    fveq2
    fveq12d
    neeq1d
    mpbiri
    necon2i
    ad2antll
    @2
    @10
    c0p
    eldifsn
    sylanbrc
    @27
    @4
    @8
    simprl
    jca
    reximi2
    anim2i
    @1
    vb
    elqaa
    sylibr
    impbii
    3bitr4ri
    eqriv
end

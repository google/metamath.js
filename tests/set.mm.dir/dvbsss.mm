include "cop.mm"
include "cdv.mm"
include "cdm.mm"
include "wcel.mm"
include "co.mm"
include "wss.mm"
include "cc.mm"
include "cpw.mm"
include "cpm.mm"
include "cvv.mm"
include "wa.mm"
include "cxp.mm"
include "wrel.mm"
include "cv.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "cnt.mm"
include "csn.mm"
include "cdif.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmpt.mm"
include "climc.mm"
include "ciun.mm"
include "df-dv.mm"
include "reldmmpt2.mm"
include "df-rel.mm"
include "mpbi.mm"
include "sseli.mm"
include "opelxp1.mm"
include "syl.mm"
include "wi.mm"
include "wceq.mm"
include "opeq1.mm"
include "eleq1d.mm"
include "eleq1.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "dmmpt2ssx.mm"
include "opeliunxp.mm"
include "sylib.mm"
include "vtoclg.mm"
include "mpcom.mm"
include "simpld.mm"
include "elpwid.mm"
include "wf.mm"
include "simprd.mm"
include "wb.mm"
include "cnex.mm"
include "elpm2g.mm"
include "sylancr.mm"
include "mpbid.mm"
include "dvbss.mm"
include "sstrd.mm"
include "wn.mm"
include "c0.mm"
include "df-ov.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "dmeqd.mm"
include "dm0.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem dvbsss
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z


  assert |- dom ( S _D F ) C_ S

  proof
    cS
    cF
    cop
    #
    cdv
    cdm
    #
    wcel
    #
    cS
    cF
    cdv
    co
    #
    cdm
    #
    cS
    wss
    @2
    @4
    cF
    cdm
    #
    cS
    @2
    @5
    cS
    cF
    @2
    cS
    cc
    @2
    cS
    cc
    cpw
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    #
    wcel
    #
    cS
    cvv
    wcel
    #
    @2
    @7
    @9
    wa
    #
    @2
    @0
    cvv
    cvv
    cxp
    #
    wcel
    @10
    @1
    @12
    @0
    @1
    wrel
    @1
    @12
    wss
    vs
    vf
    @6
    cc
    vs
    cv
    #
    cpm
    co
    #
    vx
    vf
    cv
    #
    cdm
    #
    ccnfld
    ctopn
    cfv
    @13
    crest
    co
    cnt
    cfv
    cfv
    vx
    cv
    #
    csn
    #
    vz
    @16
    @18
    cdif
    vz
    cv
    #
    @15
    cfv
    @17
    @15
    cfv
    cmin
    co
    @19
    @17
    cmin
    co
    cdiv
    co
    cmpt
    @17
    climc
    co
    cxp
    ciun
    #
    cdv
    vx
    vz
    vf
    vs
    df-dv
    #
    reldmmpt2
    @1
    df-rel
    mpbi
    sseli
    cS
    cF
    cvv
    cvv
    opelxp1
    syl
    @13
    cF
    cop
    #
    @1
    wcel
    #
    @13
    @6
    wcel
    #
    cF
    @14
    wcel
    #
    wa
    #
    wi
    @2
    @11
    wi
    vs
    cS
    cvv
    @13
    cS
    wceq
    #
    @23
    @2
    @26
    @11
    @27
    @22
    @0
    @1
    @13
    cS
    cF
    opeq1
    eleq1d
    @27
    @24
    @7
    @25
    @9
    @13
    cS
    @6
    eleq1
    @27
    @14
    @8
    cF
    @13
    cS
    cc
    cpm
    oveq2
    eleq2d
    anbi12d
    imbi12d
    @23
    @22
    vs
    @6
    @13
    csn
    @14
    cxp
    ciun
    #
    wcel
    @26
    @1
    @28
    @22
    vs
    vf
    @6
    @14
    @20
    cdv
    @21
    dmmpt2ssx
    sseli
    vs
    @6
    @14
    cF
    opeliunxp
    sylib
    vtoclg
    mpcom
    #
    simpld
    #
    elpwid
    @2
    @5
    cc
    cF
    wf
    #
    @5
    cS
    wss
    #
    @2
    @9
    @31
    @32
    wa
    #
    @2
    @7
    @9
    @29
    simprd
    @2
    cc
    cvv
    wcel
    @7
    @9
    @33
    wb
    cnex
    @30
    cc
    cS
    cF
    cvv
    @6
    elpm2g
    sylancr
    mpbid
    #
    simpld
    @2
    @31
    @32
    @34
    simprd
    #
    dvbss
    @35
    sstrd
    @2
    wn
    #
    @4
    c0
    cS
    @36
    @4
    c0
    cdm
    c0
    @36
    @3
    c0
    @36
    @3
    @0
    cdv
    cfv
    c0
    cS
    cF
    cdv
    df-ov
    @0
    cdv
    ndmfv
    syl5eq
    dmeqd
    dm0
    syl6eq
    cS
    0ss
    syl6eqss
    pm2.61i
end

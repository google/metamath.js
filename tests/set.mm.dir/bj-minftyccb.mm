include "cccinfty.mm"
include "cccbar.mm"
include "cminfty.mm"
include "bj-ccinftyssccbar.mm"
include "cpi.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "crn.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "cv.mm"
include "cc.mm"
include "cop.mm"
include "df-bj-inftyexpi.mm"
include "funmpt2.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "cc0.mm"
include "pipos.mm"
include "0re.mm"
include "ltnegi.mm"
include "mpbi.mm"
include "neg0.mm"
include "breqtri.mm"
include "lttri.mm"
include "mp2an.mm"
include "ubioc1.mm"
include "mp3an.mm"
include "opex.mm"
include "dmmpti.mm"
include "eleqtrri.mm"
include "fvelrn.mm"
include "df-bj-minfty.mm"
include "df-bj-ccinfty.mm"
include "3eltr4i.mm"
include "sselii.mm"

theorem bj-minftyccb
  let vx: setvar x


  assert |- minfty e. CCbar

  proof
    cccinfty
    cccbar
    cminfty
    bj-ccinftyssccbar
    cpi
    cinftyexpi
    cfv
    #
    cinftyexpi
    crn
    #
    cminfty
    cccinfty
    cinftyexpi
    wfun
    cpi
    cinftyexpi
    cdm
    #
    wcel
    @0
    @1
    wcel
    vx
    cpi
    cneg
    #
    cpi
    cioc
    co
    #
    vx
    cv
    #
    cc
    cop
    #
    cinftyexpi
    vx
    df-bj-inftyexpi
    #
    funmpt2
    cpi
    @4
    @2
    @3
    cxr
    wcel
    cpi
    cxr
    wcel
    @3
    cpi
    clt
    wbr
    #
    cpi
    @4
    wcel
    @3
    cpi
    pire
    renegcli
    #
    rexri
    cpi
    pire
    rexri
    @3
    cc0
    clt
    wbr
    cc0
    cpi
    clt
    wbr
    #
    @8
    @3
    cc0
    cneg
    #
    cc0
    clt
    @10
    @3
    @11
    clt
    wbr
    pipos
    cc0
    cpi
    0re
    pire
    ltnegi
    mpbi
    neg0
    breqtri
    pipos
    @3
    cc0
    cpi
    @9
    0re
    pire
    lttri
    mp2an
    @3
    cpi
    ubioc1
    mp3an
    vx
    @4
    @6
    cinftyexpi
    @5
    cc
    opex
    @7
    dmmpti
    eleqtrri
    cpi
    cinftyexpi
    fvelrn
    mp2an
    df-bj-minfty
    df-bj-ccinfty
    3eltr4i
    sselii
end

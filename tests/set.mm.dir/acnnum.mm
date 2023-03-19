include "cpw.mm"
include "wacn.mm"
include "wcel.mm"
include "ccrd.mm"
include "cdm.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wa.mm"
include "wss.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "pwexg.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "acndom.mm"
include "mpcom.mm"
include "eldifsn.mm"
include "elpwi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "rgen.mm"
include "acni2.mm"
include "sylancl.mm"
include "simpr.mm"
include "imbi1i.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii2.mm"
include "sylib.mm"
include "eximi.mm"
include "syl.mm"
include "dfac8a.mm"
include "mpd.mm"
include "numacn.mm"
include "impbii.mm"

theorem acnnum
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cY: class Y


  assert |- ( X e. AC_ ~P X <-> X e. dom card )

  proof
    cX
    cX
    cpw
    #
    wacn
    #
    wcel
    #
    cX
    ccrd
    cdm
    #
    wcel
    #
    @2
    vx
    cv
    #
    c0
    wne
    #
    @5
    vf
    cv
    #
    cfv
    @5
    wcel
    #
    wi
    #
    vx
    @0
    wral
    #
    vf
    wex
    #
    @4
    @2
    @0
    c0
    csn
    #
    cdif
    #
    cX
    @7
    wf
    #
    @8
    vx
    @13
    wral
    #
    wa
    #
    vf
    wex
    #
    @11
    @2
    cX
    @13
    wacn
    wcel
    #
    @5
    cX
    wss
    #
    @6
    wa
    #
    vx
    @13
    wral
    @17
    @13
    @0
    cdom
    wbr
    #
    @2
    @18
    @2
    @0
    cvv
    wcel
    #
    @13
    @0
    wss
    @21
    cX
    @1
    pwexg
    @0
    @12
    difss
    @13
    @0
    cvv
    ssdomg
    mpisyl
    @13
    @0
    cX
    acndom
    mpcom
    @20
    vx
    @13
    @5
    @13
    wcel
    #
    @5
    @0
    wcel
    #
    @6
    wa
    #
    @20
    @5
    @0
    c0
    eldifsn
    #
    @24
    @19
    @6
    @5
    cX
    elpwi
    anim1i
    sylbi
    rgen
    vx
    @13
    @5
    vf
    cX
    acni2
    sylancl
    @16
    @10
    vf
    @16
    @15
    @10
    @14
    @15
    simpr
    @8
    @9
    vx
    @13
    @0
    @23
    @8
    wi
    @25
    @8
    wi
    @24
    @9
    wi
    @23
    @25
    @8
    @26
    imbi1i
    @24
    @6
    @8
    impexp
    bitri
    ralbii2
    sylib
    eximi
    syl
    vx
    cX
    @1
    vf
    dfac8a
    mpd
    @22
    @4
    @2
    cX
    @3
    pwexg
    @0
    cvv
    cX
    numacn
    mpcom
    impbii
end

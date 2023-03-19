include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "c0g.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccnfld.mm"
include "cgsu.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "mdegldg.mm"
include "cvv.mm"
include "wf.mm"
include "mplrcl.mm"
include "3ad2ant2.mm"
include "tdeglem1.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "adantld.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem mdegnn0cl
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cI: class I
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let vh: setvar h
  let vm: setvar m
  assume mdeg0.d: |- D = ( I mDeg R )
  assume mdeg0.p: |- P = ( I mPoly R )
  assume mdeg0.z: |- .0. = ( 0g ` P )
  assume mdegnn0cl.b: |- B = ( Base ` P )


  assert |- ( ( R e. Ring /\ F e. B /\ F =/= .0. ) -> ( D ` F ) e. NN0 )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    #
    w3a
    #
    vx
    cv
    #
    cF
    cfv
    cR
    c0g
    cfv
    #
    wne
    #
    @4
    vh
    vm
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vm
    cn0
    cI
    cmap
    co
    crab
    #
    ccnfld
    vh
    cv
    cgsu
    co
    cmpt
    #
    cfv
    #
    cF
    cD
    cfv
    #
    wceq
    #
    wa
    #
    vx
    @7
    wrex
    @10
    cn0
    wcel
    #
    vx
    @7
    cB
    cD
    cP
    cR
    vh
    vm
    cF
    @8
    cI
    c.0
    @5
    mdeg0.d
    mdeg0.p
    mdegnn0cl.b
    @5
    eqid
    @7
    eqid
    #
    @8
    eqid
    #
    mdeg0.z
    mdegldg
    @3
    @12
    @13
    vx
    @7
    @3
    @4
    @7
    wcel
    wa
    #
    @11
    @13
    @6
    @16
    @9
    cn0
    wcel
    @11
    @13
    @3
    @7
    cn0
    @4
    @8
    @3
    cI
    cvv
    wcel
    #
    @7
    cn0
    @8
    wf
    @1
    @0
    @17
    @2
    cB
    cP
    cR
    cI
    cF
    mdeg0.p
    mdegnn0cl.b
    mplrcl
    3ad2ant2
    @7
    vh
    vm
    @8
    cI
    cvv
    @14
    @15
    tdeglem1
    syl
    ffvelrnda
    @9
    @10
    cn0
    eleq1
    syl5ibcom
    adantld
    rexlimdva
    mpd
end

include "wcel.mm"
include "ces1.mm"
include "co.mm"
include "crn.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wa.mm"
include "ne0i.mm"
include "eleq2s.mm"
include "wceq.mm"
include "rneq.mm"
include "rn0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "cop.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cdm.mm"
include "c1o.mm"
include "cmap.mm"
include "cmpt.mm"
include "ccom.mm"
include "ces.mm"
include "csb.mm"
include "df-evls1.mm"
include "dmmpt2ssx.mm"
include "elfvdm.mm"
include "df-ov.mm"
include "sseldi.mm"
include "fveq2.mm"
include "pweqd.mm"
include "opeliunxp2.mm"
include "sylib.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "3syl.mm"

theorem ply1frcl
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cX: class X
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let ve: setvar e
  assume ply1frcl.q: |- Q = ran ( S evalSub1 R )


  assert |- ( X e. Q -> ( S e. _V /\ R e. ~P ( Base ` S ) ) )

  proof
    cX
    cQ
    wcel
    cS
    cR
    ces1
    co
    #
    crn
    #
    c0
    wne
    #
    @0
    c0
    wne
    #
    cS
    cvv
    wcel
    cR
    cS
    cbs
    cfv
    #
    cpw
    #
    wcel
    wa
    #
    @2
    cX
    @1
    cQ
    @1
    cX
    ne0i
    ply1frcl.q
    eleq2s
    @0
    c0
    @1
    c0
    @0
    c0
    wceq
    @1
    c0
    crn
    c0
    @0
    c0
    rneq
    rn0
    syl6eq
    necon3i
    @3
    ve
    cv
    #
    @0
    wcel
    #
    ve
    wex
    @6
    ve
    @0
    n0
    @8
    @6
    ve
    @8
    cS
    cR
    cop
    #
    vs
    cvv
    vs
    cv
    #
    csn
    @10
    cbs
    cfv
    #
    cpw
    #
    cxp
    ciun
    #
    wcel
    @6
    @8
    ces1
    cdm
    #
    @13
    @9
    vs
    vr
    cvv
    @12
    vb
    @11
    vx
    vb
    cv
    #
    @15
    c1o
    cmap
    co
    cmap
    co
    vx
    cv
    vy
    @15
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    ccom
    cmpt
    vr
    cv
    c1o
    @10
    ces
    co
    cfv
    ccom
    csb
    ces1
    vx
    vy
    vs
    vr
    vb
    df-evls1
    dmmpt2ssx
    @9
    @14
    wcel
    @7
    @9
    ces1
    cfv
    @0
    @7
    @9
    ces1
    elfvdm
    cS
    cR
    ces1
    df-ov
    eleq2s
    sseldi
    vs
    cvv
    @12
    cS
    cR
    @5
    @10
    cS
    wceq
    @11
    @4
    @10
    cS
    cbs
    fveq2
    pweqd
    opeliunxp2
    sylib
    exlimiv
    sylbi
    3syl
end

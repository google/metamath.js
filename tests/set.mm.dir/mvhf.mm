include "cmfs.mm"
include "wcel.mm"
include "cv.mm"
include "cmty.mm"
include "cfv.mm"
include "cs1.mm"
include "cop.mm"
include "wa.mm"
include "cmtc.mm"
include "cmrex.mm"
include "cxp.mm"
include "eqid.mm"
include "mtyf2.mm"
include "ffvelrnda.mm"
include "cmcn.mm"
include "cun.mm"
include "cword.mm"
include "elun2.mm"
include "adantl.mm"
include "s1cld.mm"
include "wceq.mm"
include "mrexval.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "mexval.mm"
include "syl6eleqr.mm"
include "mvhfval.mm"
include "fmptd.mm"

theorem mvhf
  let cT: class T
  let cE: class E
  let cH: class H
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  assume mvhf.v: |- V = ( mVR ` T )
  assume mvhf.e: |- E = ( mEx ` T )
  assume mvhf.h: |- H = ( mVH ` T )


  assert |- ( T e. mFS -> H : V --> E )

  proof
    cT
    cmfs
    wcel
    #
    vv
    cV
    vv
    cv
    #
    cT
    cmty
    cfv
    #
    cfv
    #
    @1
    cs1
    #
    cop
    #
    cE
    cH
    @0
    @1
    cV
    wcel
    #
    wa
    #
    @5
    cT
    cmtc
    cfv
    #
    cT
    cmrex
    cfv
    #
    cxp
    #
    cE
    @7
    @3
    @8
    wcel
    @4
    @9
    wcel
    @5
    @10
    wcel
    @0
    cV
    @8
    @1
    @2
    cT
    @8
    cV
    @2
    mvhf.v
    @8
    eqid
    #
    @2
    eqid
    #
    mtyf2
    ffvelrnda
    @7
    @4
    cT
    cmcn
    cfv
    #
    cV
    cun
    #
    cword
    #
    @9
    @7
    @1
    @14
    @6
    @1
    @14
    wcel
    @0
    @1
    cV
    @13
    elun2
    adantl
    s1cld
    @0
    @9
    @15
    wceq
    @6
    @13
    @9
    cT
    cV
    cmfs
    @13
    eqid
    mvhf.v
    @9
    eqid
    #
    mrexval
    adantr
    eleqtrrd
    @3
    @4
    @8
    @9
    opelxpi
    syl2anc
    @9
    cT
    cE
    @8
    @11
    mvhf.e
    @16
    mexval
    syl6eleqr
    vv
    cT
    cH
    cV
    @2
    mvhf.v
    @12
    mvhf.h
    mvhfval
    fmptd
end

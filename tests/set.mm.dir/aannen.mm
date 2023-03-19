include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0p.mm"
include "wne.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "ccoe.mm"
include "cabs.mm"
include "wral.mm"
include "w3a.mm"
include "cz.mm"
include "cply.mm"
include "crab.mm"
include "wrex.mm"
include "cc.mm"
include "cmpt.mm"
include "eqid.mm"
include "aannenlem3.mm"

theorem aannen
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e


  assert |- AA ~~ NN

  proof
    ve
    va
    cn0
    vb
    cv
    vc
    cv
    cfv
    cc0
    wceq
    vc
    vd
    cv
    #
    c0p
    wne
    @0
    cdgr
    cfv
    va
    cv
    #
    cle
    wbr
    ve
    cv
    @0
    ccoe
    cfv
    cfv
    cabs
    cfv
    @1
    cle
    wbr
    ve
    cn0
    wral
    w3a
    vd
    cz
    cply
    cfv
    crab
    wrex
    vb
    cc
    crab
    cmpt
    #
    va
    vb
    vc
    vd
    @2
    eqid
    aannenlem3
end

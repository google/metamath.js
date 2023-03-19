include "cbo.mm"
include "wcel.mm"
include "cado.mm"
include "cfv.mm"
include "adjbdln.mm"
include "cdm.mm"
include "bdopadj.mm"
include "dmadjrnb.mm"
include "sylibr.mm"
include "wa.mm"
include "ccnv.mm"
include "cnvadj.mm"
include "fveq1i.mm"
include "wf1o.mm"
include "wceq.mm"
include "adj1o.mm"
include "simpl.mm"
include "f1ocnvfv1.mm"
include "sylancr.mm"
include "syl5eqr.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "mpancom.mm"
include "impbii.mm"

theorem adjbdlnb
  let cT: class T
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. BndLinOp <-> ( adjh ` T ) e. BndLinOp )

  proof
    cT
    cbo
    wcel
    #
    cT
    cado
    cfv
    #
    cbo
    wcel
    #
    cT
    adjbdln
    cT
    cado
    cdm
    #
    wcel
    #
    @2
    @0
    @2
    @1
    @3
    wcel
    @4
    @1
    bdopadj
    cT
    dmadjrnb
    sylibr
    @4
    @2
    wa
    #
    @1
    cado
    cfv
    #
    cT
    cbo
    @5
    @6
    @1
    cado
    ccnv
    #
    cfv
    #
    cT
    @1
    @7
    cado
    cnvadj
    fveq1i
    @5
    @3
    @3
    cado
    wf1o
    @4
    @8
    cT
    wceq
    adj1o
    @4
    @2
    simpl
    @3
    @3
    cT
    cado
    f1ocnvfv1
    sylancr
    syl5eqr
    @2
    @6
    cbo
    wcel
    @4
    @1
    adjbdln
    adantl
    eqeltrrd
    mpancom
    impbii
end

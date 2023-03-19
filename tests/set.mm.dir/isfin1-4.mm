include "wcel.mm"
include "cfn.mm"
include "cpw.mm"
include "crpss.mm"
include "ccnv.mm"
include "wfr.mm"
include "isfin1-3.mm"
include "cv.mm"
include "cdif.mm"
include "cmpt.mm"
include "wiso.mm"
include "wb.mm"
include "eqid.mm"
include "compssiso.mm"
include "isofr.mm"
include "syl.mm"
include "bitr4d.mm"

theorem isfin1-4
  let cA: class A
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( A e. V -> ( A e. Fin <-> [C.] Fr ~P A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfn
    wcel
    cA
    cpw
    #
    crpss
    ccnv
    #
    wfr
    #
    @1
    crpss
    wfr
    #
    cA
    cV
    isfin1-3
    @0
    @1
    @1
    crpss
    @2
    vx
    @1
    cA
    vx
    cv
    cdif
    cmpt
    #
    wiso
    @4
    @3
    wb
    vx
    cA
    @5
    cV
    @5
    eqid
    compssiso
    @1
    @1
    crpss
    @2
    @5
    isofr
    syl
    bitr4d
end

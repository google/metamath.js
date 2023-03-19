include "carea.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cvol.mm"
include "cfv.mm"
include "citg.mm"
include "dfarea.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "areambl.mm"
include "simprd.mm"
include "cxp.mm"
include "wss.mm"
include "ccnv.mm"
include "wral.mm"
include "cmpt.mm"
include "cibl.mm"
include "dmarea.mm"
include "simp3bi.mm"
include "itgrecl.mm"
include "covol.mm"
include "simpld.mm"
include "mblss.mm"
include "ovolge0.mm"
include "3syl.mm"
include "wceq.mm"
include "mblvol.mm"
include "syl.mm"
include "breqtrrd.mm"
include "itgge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "fmpti.mm"

theorem areaf
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cS: class S


  assert |- area : dom area --> ( 0 [,) +oo )

  proof
    vs
    carea
    cdm
    #
    cc0
    cpnf
    cico
    co
    #
    vx
    cr
    vs
    cv
    #
    vx
    cv
    #
    csn
    cima
    #
    cvol
    cfv
    #
    citg
    #
    carea
    vx
    vs
    dfarea
    @2
    @0
    wcel
    #
    @6
    cr
    wcel
    cc0
    @6
    cle
    wbr
    @6
    @1
    wcel
    @7
    vx
    cr
    @5
    @7
    @3
    cr
    wcel
    wa
    #
    @4
    cvol
    cdm
    wcel
    #
    @5
    cr
    wcel
    #
    @3
    @2
    areambl
    #
    simprd
    #
    @7
    @2
    cr
    cr
    cxp
    wss
    @4
    cvol
    ccnv
    cr
    cima
    wcel
    vx
    cr
    wral
    vx
    cr
    @5
    cmpt
    cibl
    wcel
    vx
    @2
    dmarea
    simp3bi
    #
    itgrecl
    @7
    vx
    cr
    @5
    @13
    @12
    @8
    cc0
    @4
    covol
    cfv
    #
    @5
    cle
    @8
    @9
    @4
    cr
    wss
    cc0
    @14
    cle
    wbr
    @8
    @9
    @10
    @11
    simpld
    #
    @4
    mblss
    @4
    ovolge0
    3syl
    @8
    @9
    @5
    @14
    wceq
    @15
    @4
    mblvol
    syl
    breqtrrd
    itgge0
    @6
    elrege0
    sylanbrc
    fmpti
end

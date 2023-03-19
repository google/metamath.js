include "c0.mm"
include "cmbf.mm"
include "wcel.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "cnv0.mm"
include "imaeq1i.mm"
include "0ima.mm"
include "0mbl.mm"
include "eqeltri.mm"
include "rgenw.mm"
include "cr.mm"
include "wf.mm"
include "wb.mm"
include "f0.mm"
include "ismbf.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem mbf0
  let vk: setvar k
  let vx: setvar x


  assert |- (/) e. MblFn

  proof
    c0
    cmbf
    wcel
    #
    c0
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    vx
    cioo
    crn
    #
    wral
    #
    @5
    vx
    @6
    @3
    c0
    @2
    cima
    #
    @4
    @1
    c0
    @2
    cnv0
    imaeq1i
    @8
    c0
    @4
    @2
    0ima
    0mbl
    eqeltri
    eqeltri
    rgenw
    c0
    cr
    c0
    wf
    @0
    @7
    wb
    cr
    f0
    vx
    c0
    c0
    ismbf
    ax-mp
    mpbir
end

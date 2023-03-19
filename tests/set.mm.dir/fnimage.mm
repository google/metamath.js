include "cimage.mm"
include "cv.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "cab.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "funimage.mm"
include "wbr.mm"
include "wex.mm"
include "vex.mm"
include "brimage.mm"
include "eqvisset.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "eqid.mm"
include "wb.mm"
include "brimageg.mm"
include "mpan.mm"
include "mpbiri.mm"
include "breq2.mm"
include "spcegv.mm"
include "mpd.mm"
include "impbii.mm"
include "eldm.mm"
include "weq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "elab.mm"
include "3bitr4i.mm"
include "eqriv.mm"
include "df-fn.mm"
include "mpbir2an.mm"

theorem fnimage
  let vx: setvar x
  let cR: class R
  let vy: setvar y

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- Image R Fn { x | ( R " x ) e. _V }

  proof
    cR
    cimage
    #
    cR
    vx
    cv
    #
    cima
    #
    cvv
    wcel
    #
    vx
    cab
    #
    wfn
    @0
    wfun
    @0
    cdm
    #
    @4
    wceq
    cR
    funimage
    vy
    @5
    @4
    vy
    cv
    #
    @1
    @0
    wbr
    #
    vx
    wex
    #
    cR
    @6
    cima
    #
    cvv
    wcel
    #
    @6
    @5
    wcel
    @6
    @4
    wcel
    @8
    @10
    @7
    @10
    vx
    @7
    @1
    @9
    wceq
    @10
    @6
    @1
    cR
    vy
    vex
    #
    vx
    vex
    brimage
    vx
    @9
    eqvisset
    sylbi
    exlimiv
    @10
    @6
    @9
    @0
    wbr
    #
    @8
    @10
    @12
    @9
    @9
    wceq
    #
    @9
    eqid
    @6
    cvv
    wcel
    @10
    @12
    @13
    wb
    @11
    @6
    @9
    cR
    cvv
    cvv
    brimageg
    mpan
    mpbiri
    @7
    @12
    vx
    @9
    cvv
    @1
    @9
    @6
    @0
    breq2
    spcegv
    mpd
    impbii
    vx
    @6
    @0
    @11
    eldm
    @3
    @10
    vx
    @6
    @11
    vx
    vy
    weq
    @2
    @9
    cvv
    @1
    @6
    cR
    imaeq2
    eleq1d
    elab
    3bitr4i
    eqriv
    @0
    @4
    df-fn
    mpbir2an
end

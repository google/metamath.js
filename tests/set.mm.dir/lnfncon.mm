include "clf.mm"
include "wcel.mm"
include "ccnfn.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wb.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cif.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rexralbidv.mm"
include "bibi12d.mm"
include "0lnfn.mm"
include "elimel.mm"
include "lnfnconi.mm"
include "dedth.mm"

theorem lnfncon
  let vx: setvar x
  let vy: setvar y
  let cT: class T

  disjoint x y
  disjoint T x
  disjoint T y
  assert |- ( T e. LinFn -> ( T e. ContFn <-> E. x e. RR A. y e. ~H ( abs ` ( T ` y ) ) <_ ( x x. ( normh ` y ) ) ) )

  proof
    cT
    clf
    wcel
    #
    cT
    ccnfn
    wcel
    #
    vy
    cv
    #
    cT
    cfv
    #
    cabs
    cfv
    #
    vx
    cv
    @2
    cno
    cfv
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    vx
    cr
    wrex
    #
    wb
    @0
    cT
    chil
    cc0
    csn
    cxp
    #
    cif
    #
    ccnfn
    wcel
    #
    @2
    @9
    cfv
    #
    cabs
    cfv
    #
    @5
    cle
    wbr
    #
    vy
    chil
    wral
    vx
    cr
    wrex
    #
    wb
    cT
    @8
    cT
    @9
    wceq
    #
    @1
    @10
    @7
    @14
    cT
    @9
    ccnfn
    eleq1
    @15
    @6
    @13
    vx
    vy
    cr
    chil
    @15
    @4
    @12
    @5
    cle
    @15
    @3
    @11
    cabs
    @2
    cT
    @9
    fveq1
    fveq2d
    breq1d
    rexralbidv
    bibi12d
    vx
    vy
    @9
    cT
    @8
    clf
    0lnfn
    elimel
    lnfnconi
    dedth
end

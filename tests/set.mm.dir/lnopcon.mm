include "clo.mm"
include "wcel.mm"
include "ccop.mm"
include "cv.mm"
include "cfv.mm"
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
include "cid.mm"
include "cres.mm"
include "cif.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rexralbidv.mm"
include "bibi12d.mm"
include "idlnop.mm"
include "elimel.mm"
include "lnopconi.mm"
include "dedth.mm"

theorem lnopcon
  let vx: setvar x
  let vy: setvar y
  let cT: class T

  disjoint x y
  disjoint T x
  disjoint T y
  assert |- ( T e. LinOp -> ( T e. ContOp <-> E. x e. RR A. y e. ~H ( normh ` ( T ` y ) ) <_ ( x x. ( normh ` y ) ) ) )

  proof
    cT
    clo
    wcel
    #
    cT
    ccop
    wcel
    #
    vy
    cv
    #
    cT
    cfv
    #
    cno
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
    cid
    chil
    cres
    #
    cif
    #
    ccop
    wcel
    #
    @2
    @9
    cfv
    #
    cno
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
    ccop
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
    cno
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
    clo
    idlnop
    elimel
    lnopconi
    dedth
end

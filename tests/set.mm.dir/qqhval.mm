include "cz.mm"
include "cv.mm"
include "czrh.mm"
include "cfv.mm"
include "ccnv.mm"
include "cui.mm"
include "cima.mm"
include "cdiv.mm"
include "co.mm"
include "cdvr.mm"
include "cop.mm"
include "cmpt2.mm"
include "crn.mm"
include "cvv.mm"
include "cqqh.mm"
include "wceq.mm"
include "eqidd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "imaeq12d.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "opeq2d.mm"
include "mpt2eq123dv.mm"
include "rneqd.mm"
include "df-qqh.mm"
include "zex.mm"
include "wcel.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cnvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "mpt2ex.mm"
include "rnex.mm"
include "fvmpt.mm"

theorem qqhval
  let vx: setvar x
  let vy: setvar y
  let c.dv: class ./
  let cR: class R
  let c.1: class .1.
  let cL: class L
  let vf: setvar f
  assume qqhval.1: |- ./ = ( /r ` R )
  assume qqhval.2: |- .1. = ( 1r ` R )
  assume qqhval.3: |- L = ( ZRHom ` R )

  disjoint x y
  disjoint R x
  disjoint R y
  disjoint L y
  disjoint f x
  disjoint f y
  disjoint R f
  disjoint ./ f
  disjoint L f
  assert |- ( R e. _V -> ( QQHom ` R ) = ran ( x e. ZZ , y e. ( `' L " ( Unit ` R ) ) |-> <. ( x / y ) , ( ( L ` x ) ./ ( L ` y ) ) >. ) )

  proof
    vf
    cR
    vx
    vy
    cz
    vf
    cv
    #
    czrh
    cfv
    #
    ccnv
    #
    @0
    cui
    cfv
    #
    cima
    #
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    @5
    @1
    cfv
    #
    @6
    @1
    cfv
    #
    @0
    cdvr
    cfv
    #
    co
    #
    cop
    #
    cmpt2
    #
    crn
    vx
    vy
    cz
    cL
    ccnv
    #
    cR
    cui
    cfv
    #
    cima
    #
    @7
    @5
    cL
    cfv
    #
    @6
    cL
    cfv
    #
    c.dv
    co
    #
    cop
    #
    cmpt2
    #
    crn
    cvv
    cqqh
    @0
    cR
    wceq
    #
    @13
    @21
    @22
    vx
    vy
    cz
    @4
    @12
    cz
    @16
    @20
    @22
    cz
    eqidd
    @22
    @2
    @14
    @3
    @15
    @22
    @1
    cL
    @22
    @1
    cR
    czrh
    cfv
    #
    cL
    @0
    cR
    czrh
    fveq2
    qqhval.3
    syl6eqr
    #
    cnveqd
    @0
    cR
    cui
    fveq2
    imaeq12d
    @22
    @11
    @19
    @7
    @22
    @8
    @17
    @9
    @18
    @10
    c.dv
    @22
    @10
    cR
    cdvr
    cfv
    c.dv
    @0
    cR
    cdvr
    fveq2
    qqhval.1
    syl6eqr
    @22
    @5
    @1
    cL
    @24
    fveq1d
    @22
    @6
    @1
    cL
    @24
    fveq1d
    oveq123d
    opeq2d
    mpt2eq123dv
    rneqd
    vx
    vy
    vf
    df-qqh
    @21
    vx
    vy
    cz
    @16
    @20
    zex
    @14
    cvv
    wcel
    @16
    cvv
    wcel
    cL
    cL
    @23
    cvv
    qqhval.3
    cR
    czrh
    fvex
    eqeltri
    cnvex
    @14
    @15
    cvv
    imaexg
    ax-mp
    mpt2ex
    rnex
    fvmpt
end

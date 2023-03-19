include "cmnd.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cds.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cbs.mm"
include "c0g.mm"
include "cres.mm"
include "cnm.mm"
include "wceq.mm"
include "ressbas2.mm"
include "3ad2ant3.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "eqid.mm"
include "ressds.mm"
include "syl.mm"
include "eqidd.mm"
include "ress0g.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "nmfval.mm"
include "reseq1i.mm"
include "resmpt.mm"
include "syl5eq.mm"
include "a1i.mm"
include "3eqtr4d.mm"

theorem ressnm
  let cA: class A
  let cB: class B
  let cG: class G
  let cH: class H
  let cN: class N
  let c.0: class .0.
  let vx: setvar x
  assume ressnm.1: |- H = ( G |`s A )
  assume ressnm.2: |- B = ( Base ` G )
  assume ressnm.3: |- .0. = ( 0g ` G )
  assume ressnm.4: |- N = ( norm ` G )


  assert |- ( ( G e. Mnd /\ .0. e. A /\ A C_ B ) -> ( N |` A ) = ( norm ` H ) )

  proof
    cG
    cmnd
    wcel
    #
    c.0
    cA
    wcel
    #
    cA
    cB
    wss
    #
    w3a
    #
    vx
    cA
    vx
    cv
    #
    c.0
    cG
    cds
    cfv
    #
    co
    #
    cmpt
    #
    vx
    cH
    cbs
    cfv
    #
    @4
    cH
    c0g
    cfv
    #
    cH
    cds
    cfv
    #
    co
    #
    cmpt
    #
    cN
    cA
    cres
    #
    cH
    cnm
    cfv
    #
    @3
    vx
    cA
    @6
    @8
    @11
    @2
    @0
    cA
    @8
    wceq
    @1
    cA
    cB
    cH
    cG
    ressnm.1
    ressnm.2
    ressbas2
    3ad2ant3
    @3
    @4
    @4
    c.0
    @9
    @5
    @10
    @2
    @0
    @5
    @10
    wceq
    #
    @1
    @2
    cA
    cvv
    wcel
    @15
    cA
    cB
    cB
    cG
    cbs
    cfv
    cvv
    ressnm.2
    cG
    cbs
    fvex
    eqeltri
    ssex
    cA
    @5
    cG
    cH
    cvv
    ressnm.1
    @5
    eqid
    #
    ressds
    syl
    3ad2ant3
    @3
    @4
    eqidd
    cA
    cB
    cG
    cH
    c.0
    ressnm.1
    ressnm.2
    ressnm.3
    ress0g
    oveq123d
    mpteq12dv
    @2
    @0
    @13
    @7
    wceq
    @1
    @2
    @13
    vx
    cB
    @6
    cmpt
    #
    cA
    cres
    @7
    cN
    @17
    cA
    vx
    @5
    cN
    cG
    cB
    c.0
    ressnm.4
    ressnm.2
    ressnm.3
    @16
    nmfval
    reseq1i
    vx
    cB
    cA
    @6
    resmpt
    syl5eq
    3ad2ant3
    @14
    @12
    wceq
    @3
    vx
    @10
    @14
    cH
    @8
    @9
    @14
    eqid
    @8
    eqid
    @9
    eqid
    @10
    eqid
    nmfval
    a1i
    3eqtr4d
end

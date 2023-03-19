include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csca.mm"
include "cbs.mm"
include "cv.mm"
include "cur.mm"
include "cvsca.mm"
include "co.mm"
include "cmpt.mm"
include "cascl.mm"
include "eqid.mm"
include "resssca.mm"
include "fveq2d.mm"
include "ressvsca.mm"
include "eqidd.mm"
include "subrg1.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "asclfval.mm"
include "3eqtr4g.mm"

theorem ressascl
  let cA: class A
  let cS: class S
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume ressascl.a: |- A = ( algSc ` W )
  assume ressascl.x: |- X = ( W |`s S )


  assert |- ( S e. ( SubRing ` W ) -> A = ( algSc ` X ) )

  proof
    cS
    cW
    csubrg
    cfv
    #
    wcel
    #
    vx
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    vx
    cv
    #
    cW
    cur
    cfv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cmpt
    vx
    cX
    csca
    cfv
    #
    cbs
    cfv
    #
    @4
    cX
    cur
    cfv
    #
    cX
    cvsca
    cfv
    #
    co
    #
    cmpt
    cA
    cX
    cascl
    cfv
    #
    @1
    vx
    @3
    @7
    @9
    @12
    @1
    @2
    @8
    cbs
    cS
    @2
    cW
    cX
    @0
    ressascl.x
    @2
    eqid
    #
    resssca
    fveq2d
    @1
    @4
    @4
    @5
    @10
    @6
    @11
    cS
    @6
    cW
    cX
    @0
    ressascl.x
    @6
    eqid
    #
    ressvsca
    @1
    @4
    eqidd
    cS
    cW
    cX
    @5
    ressascl.x
    @5
    eqid
    #
    subrg1
    oveq123d
    mpteq12dv
    vx
    cA
    @6
    @5
    @2
    @3
    cW
    ressascl.a
    @14
    @3
    eqid
    @15
    @16
    asclfval
    vx
    @13
    @11
    @10
    @8
    @9
    cX
    @13
    eqid
    @8
    eqid
    @9
    eqid
    @11
    eqid
    @10
    eqid
    asclfval
    3eqtr4g
end

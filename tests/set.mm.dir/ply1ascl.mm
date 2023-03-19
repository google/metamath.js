include "cascl.mm"
include "cfv.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "csca.mm"
include "eqid.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "con0.mm"
include "1on.mm"
include "a1i.mm"
include "id.mm"
include "mplsca.mm"
include "cv.mm"
include "wa.mm"
include "cvsca.mm"
include "ply1vsca.mm"
include "oveqdr.mm"
include "cur.mm"
include "ply1mpl1.mm"
include "fvexd.mm"
include "asclpropd.mm"
include "wn.mm"
include "c0.mm"
include "cpl1.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "reldmmpl.mm"
include "ovprc2.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem ply1ascl
  let cA: class A
  let cP: class P
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume ply1ascl.p: |- P = ( Poly1 ` R )
  assume ply1ascl.a: |- A = ( algSc ` P )


  assert |- A = ( algSc ` ( 1o mPoly R ) )

  proof
    cA
    cP
    cascl
    cfv
    #
    c1o
    cR
    cmpl
    co
    #
    cascl
    cfv
    #
    ply1ascl.a
    cR
    cvv
    wcel
    #
    @0
    @2
    wceq
    @3
    vx
    vy
    cR
    cbs
    cfv
    #
    cP
    csca
    cfv
    #
    @1
    csca
    cfv
    #
    cP
    @1
    cvv
    @5
    eqid
    @6
    eqid
    @3
    cR
    @5
    cbs
    cP
    cR
    cvv
    ply1ascl.p
    ply1sca
    fveq2d
    @3
    cR
    @6
    cbs
    @3
    @1
    cR
    c1o
    con0
    cvv
    @1
    eqid
    #
    c1o
    con0
    wcel
    @3
    1on
    a1i
    @3
    id
    mplsca
    fveq2d
    @3
    vx
    cv
    @4
    wcel
    vy
    cv
    cvv
    wcel
    wa
    vx
    vy
    cP
    cvsca
    cfv
    #
    @1
    cvsca
    cfv
    #
    @8
    @9
    wceq
    @3
    cR
    @1
    @8
    cP
    ply1ascl.p
    @7
    @8
    eqid
    ply1vsca
    a1i
    oveqdr
    cP
    cur
    cfv
    #
    @1
    cur
    cfv
    wceq
    @3
    cP
    cR
    @10
    @1
    @7
    ply1ascl.p
    @10
    eqid
    ply1mpl1
    a1i
    @3
    cP
    cur
    fvexd
    asclpropd
    @3
    wn
    #
    cP
    @1
    cascl
    @11
    cP
    c0
    @1
    @11
    cP
    cR
    cpl1
    cfv
    c0
    ply1ascl.p
    cR
    cpl1
    fvprc
    syl5eq
    c1o
    cR
    cmpl
    reldmmpl
    ovprc2
    eqtr4d
    fveq2d
    pm2.61i
    eqtri
end

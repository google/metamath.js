include "cmnd.mm"
include "wcel.mm"
include "w3a.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "co.mm"
include "cbs.mm"
include "cv.mm"
include "cmpt.mm"
include "cmhm.mm"
include "cvv.mm"
include "eqid.mm"
include "simp2.mm"
include "fvexd.mm"
include "wf.mm"
include "fconst6g.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "prdspjmhm.mm"
include "wceq.mm"
include "pwsval.mm"
include "3adant3.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "fvconst2g.mm"
include "3adant2.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "3eltr4d.mm"

theorem pwspjmhm
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cI: class I
  let cV: class V
  let cY: class Y
  assume pwspjmhm.y: |- Y = ( R ^s I )
  assume pwspjmhm.b: |- B = ( Base ` Y )

  disjoint A x
  disjoint B x
  disjoint I x
  disjoint R x
  disjoint V x
  assert |- ( ( R e. Mnd /\ I e. V /\ A e. I ) -> ( x e. B |-> ( x ` A ) ) e. ( Y MndHom R ) )

  proof
    cR
    cmnd
    wcel
    #
    cI
    cV
    wcel
    #
    cA
    cI
    wcel
    #
    w3a
    #
    vx
    cR
    csca
    cfv
    #
    cI
    cR
    csn
    cxp
    #
    cprds
    co
    #
    cbs
    cfv
    #
    cA
    vx
    cv
    cfv
    #
    cmpt
    @6
    cA
    @5
    cfv
    #
    cmhm
    co
    vx
    cB
    @8
    cmpt
    cY
    cR
    cmhm
    co
    @3
    vx
    cA
    @7
    @5
    @4
    cI
    cV
    cvv
    @6
    @6
    eqid
    @7
    eqid
    @0
    @1
    @2
    simp2
    @3
    cR
    csca
    fvexd
    @0
    @1
    cI
    cmnd
    @5
    wf
    @2
    cI
    cR
    cmnd
    fconst6g
    3ad2ant1
    @0
    @1
    @2
    simp3
    prdspjmhm
    @3
    vx
    cB
    @7
    @8
    @3
    cB
    cY
    cbs
    cfv
    @7
    pwspjmhm.b
    @3
    cY
    @6
    cbs
    @0
    @1
    cY
    @6
    wceq
    @2
    cR
    @4
    cI
    cmnd
    cV
    cY
    pwspjmhm.y
    @4
    eqid
    pwsval
    3adant3
    #
    fveq2d
    syl5eq
    mpteq1d
    @3
    cY
    @6
    cR
    @9
    cmhm
    @10
    @3
    @9
    cR
    @0
    @2
    @9
    cR
    wceq
    @1
    cI
    cR
    cA
    cmnd
    fvconst2g
    3adant2
    eqcomd
    oveq12d
    3eltr4d
end

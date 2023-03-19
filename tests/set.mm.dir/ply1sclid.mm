include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfv.mm"
include "cco1.mm"
include "cn0.mm"
include "cv.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "coe1scl.mm"
include "fveq1d.mm"
include "0nn0.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "mpan.mm"
include "adantl.mm"
include "eqtr2d.mm"

theorem ply1sclid
  let cA: class A
  let cP: class P
  let cR: class R
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let c.0: class .0.
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume ply1sclid.k: |- K = ( Base ` R )


  assert |- ( ( R e. Ring /\ X e. K ) -> X = ( ( coe1 ` ( A ` X ) ) ` 0 ) )

  proof
    cR
    crg
    wcel
    #
    cX
    cK
    wcel
    #
    wa
    #
    cc0
    cX
    cA
    cfv
    cco1
    cfv
    #
    cfv
    cc0
    vx
    cn0
    vx
    cv
    cc0
    wceq
    #
    cX
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cfv
    #
    cX
    @2
    cc0
    @3
    @7
    vx
    cA
    cP
    cR
    cK
    cX
    @5
    ply1scl.p
    ply1scl.a
    ply1sclid.k
    @5
    eqid
    coe1scl
    fveq1d
    @1
    @8
    cX
    wceq
    #
    @0
    cc0
    cn0
    wcel
    @1
    @9
    0nn0
    vx
    cc0
    @6
    cX
    cn0
    cK
    @7
    @4
    cX
    @5
    iftrue
    @7
    eqid
    fvmptg
    mpan
    adantl
    eqtr2d
end

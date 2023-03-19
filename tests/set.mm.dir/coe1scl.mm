include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cco1.mm"
include "cc0.mm"
include "cv1.mm"
include "cmgp.mm"
include "cmg.mm"
include "co.mm"
include "cvsca.mm"
include "cn0.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "eqid.mm"
include "ply1scltm.mm"
include "fveq2d.mm"
include "0nn0.mm"
include "coe1tm.mm"
include "mp3an3.mm"
include "eqtrd.mm"

theorem coe1scl
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cR: class R
  let cK: class K
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume coe1scl.k: |- K = ( Base ` R )
  assume coe1scl.z: |- .0. = ( 0g ` R )

  disjoint A x
  disjoint K x
  disjoint P x
  disjoint R x
  disjoint X x
  disjoint .0. x
  disjoint x y
  disjoint A y
  disjoint K y
  disjoint R y
  assert |- ( ( R e. Ring /\ X e. K ) -> ( coe1 ` ( A ` X ) ) = ( x e. NN0 |-> if ( x = 0 , X , .0. ) ) )

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
    cX
    cA
    cfv
    #
    cco1
    cfv
    cX
    cc0
    cR
    cv1
    cfv
    #
    cP
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    cP
    cvsca
    cfv
    #
    co
    #
    cco1
    cfv
    #
    vx
    cn0
    vx
    cv
    cc0
    wceq
    cX
    c.0
    cif
    cmpt
    #
    @2
    @3
    @8
    cco1
    cA
    cP
    cR
    @7
    @6
    cX
    cK
    @5
    @4
    coe1scl.k
    ply1scl.p
    @4
    eqid
    #
    @7
    eqid
    #
    @5
    eqid
    #
    @6
    eqid
    #
    ply1scl.a
    ply1scltm
    fveq2d
    @0
    @1
    cc0
    cn0
    wcel
    @9
    @10
    wceq
    0nn0
    vx
    cX
    cc0
    cP
    cR
    @7
    @6
    cK
    @5
    @4
    c.0
    coe1scl.z
    coe1scl.k
    ply1scl.p
    @11
    @12
    @13
    @14
    coe1tm
    mp3an3
    eqtrd
end

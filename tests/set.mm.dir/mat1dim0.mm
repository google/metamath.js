include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "cfv.mm"
include "csn.mm"
include "cmpt2.mm"
include "cop.mm"
include "cfn.mm"
include "wceq.mm"
include "snfi.mm"
include "a1i.mm"
include "anim2i.mm"
include "ancomd.mm"
include "eqid.mm"
include "mat0op.mm"
include "syl.mm"
include "cvv.mm"
include "simpr.mm"
include "fvexd.mm"
include "w3a.mm"
include "cv.mm"
include "eqidd.mm"
include "mpt2sn.mm"
include "eqcomi.mm"
include "opeq1i.mm"
include "sneqi.mm"
include "syl6eq.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem mat1dim0
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cO: class O
  let cV: class V
  let vr: setvar r
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mat1dim.a: |- A = ( { E } Mat R )
  assume mat1dim.b: |- B = ( Base ` R )
  assume mat1dim.o: |- O = <. E , E >.


  assert |- ( ( R e. Ring /\ E e. V ) -> ( 0g ` A ) = { <. O , ( 0g ` R ) >. } )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cA
    c0g
    cfv
    #
    vx
    vy
    cE
    csn
    #
    @4
    cR
    c0g
    cfv
    #
    cmpt2
    #
    cO
    @5
    cop
    #
    csn
    #
    @2
    @4
    cfn
    wcel
    #
    @0
    wa
    @3
    @6
    wceq
    @2
    @0
    @9
    @1
    @9
    @0
    @9
    @1
    cE
    snfi
    a1i
    anim2i
    ancomd
    cA
    cR
    vx
    vy
    @4
    @5
    mat1dim.a
    @5
    eqid
    mat0op
    syl
    @2
    @1
    @1
    @5
    cvv
    wcel
    #
    @6
    @8
    wceq
    @0
    @1
    simpr
    #
    @11
    @2
    cR
    c0g
    fvexd
    @1
    @1
    @10
    w3a
    @6
    cE
    cE
    cop
    #
    @5
    cop
    #
    csn
    @8
    vx
    vy
    cE
    cE
    @5
    @5
    cvv
    @5
    @6
    cV
    cV
    @6
    eqid
    vx
    cv
    cE
    wceq
    @5
    eqidd
    vy
    cv
    cE
    wceq
    @5
    eqidd
    mpt2sn
    @13
    @7
    @12
    cO
    @5
    cO
    @12
    mat1dim.o
    eqcomi
    opeq1i
    sneqi
    syl6eq
    syl3anc
    eqtrd
end

include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "csn.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "cop.mm"
include "cfn.mm"
include "wceq.mm"
include "snfi.mm"
include "a1i.mm"
include "anim2i.mm"
include "ancomd.mm"
include "eqid.mm"
include "mat1.mm"
include "syl.mm"
include "cvv.mm"
include "simpr.mm"
include "fvex.mm"
include "ifex.mm"
include "cv.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqeq2.mm"
include "mpt2sn.mm"
include "syl3anc.mm"
include "iftruei.mm"
include "opeq2i.mm"
include "sneqi.mm"
include "syl6eq.mm"
include "opeq1i.mm"
include "syl6eqr.mm"
include "eqtrd.mm"

theorem mat1dimid
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


  assert |- ( ( R e. Ring /\ E e. V ) -> ( 1r ` A ) = { <. O , ( 1r ` R ) >. } )

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
    cur
    cfv
    #
    vx
    vy
    cE
    csn
    #
    @4
    vx
    vy
    weq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt2
    #
    cO
    @6
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
    @9
    wceq
    @2
    @0
    @12
    @1
    @12
    @0
    @12
    @1
    cE
    snfi
    a1i
    anim2i
    ancomd
    cA
    cR
    @6
    vx
    vy
    @4
    @7
    mat1dim.a
    @6
    eqid
    @7
    eqid
    mat1
    syl
    @2
    @9
    cE
    cE
    cop
    #
    @6
    cop
    #
    csn
    #
    @11
    @2
    @9
    @13
    cE
    cE
    wceq
    #
    @6
    @7
    cif
    #
    cop
    #
    csn
    #
    @15
    @2
    @1
    @1
    @17
    cvv
    wcel
    #
    @9
    @19
    wceq
    @0
    @1
    simpr
    #
    @21
    @20
    @2
    @16
    @6
    @7
    cR
    cur
    fvex
    cR
    c0g
    fvex
    ifex
    a1i
    vx
    vy
    cE
    cE
    @8
    cE
    vy
    cv
    #
    wceq
    #
    @6
    @7
    cif
    cvv
    @17
    @9
    cV
    cV
    @9
    eqid
    vx
    cv
    #
    cE
    wceq
    @5
    @23
    @6
    @7
    @24
    cE
    @22
    eqeq1
    ifbid
    @22
    cE
    wceq
    @23
    @16
    @6
    @7
    @22
    cE
    cE
    eqeq2
    ifbid
    mpt2sn
    syl3anc
    @18
    @14
    @17
    @6
    @13
    @16
    @6
    @7
    cE
    eqid
    iftruei
    opeq2i
    sneqi
    syl6eq
    @10
    @14
    cO
    @13
    @6
    mat1dim.o
    opeq1i
    sneqi
    syl6eqr
    eqtrd
end

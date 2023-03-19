include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "wf.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cur.mm"
include "w3a.mm"
include "cmhm.mm"
include "crg.mm"
include "crngring.mm"
include "matring.mm"
include "sylan2.mm"
include "eqid.mm"
include "ringmgp.mm"
include "syl.mm"
include "ply1ring.mm"
include "jca.mm"
include "mat2pmatf.mm"
include "mat2pmatmul.mm"
include "mat2pmat1.mm"
include "3jca.mm"
include "mgpbas.mm"
include "mgpplusg.mm"
include "ringidval.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem mat2pmatmhm
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let cH: class H
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let vm: setvar m
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume mat2pmatbas.t: |- T = ( N matToPolyMat R )
  assume mat2pmatbas.a: |- A = ( N Mat R )
  assume mat2pmatbas.b: |- B = ( Base ` A )
  assume mat2pmatbas.p: |- P = ( Poly1 ` R )
  assume mat2pmatbas.c: |- C = ( N Mat P )
  assume mat2pmatbas0.h: |- H = ( Base ` C )


  assert |- ( ( N e. Fin /\ R e. CRing ) -> T e. ( ( mulGrp ` A ) MndHom ( mulGrp ` C ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    wa
    #
    cA
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    cC
    cmgp
    cfv
    #
    cmnd
    wcel
    #
    wa
    cB
    cH
    cT
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cA
    cmulr
    cfv
    #
    co
    cT
    cfv
    @8
    cT
    cfv
    @9
    cT
    cfv
    cC
    cmulr
    cfv
    #
    co
    wceq
    vy
    cB
    wral
    vx
    cB
    wral
    #
    cA
    cur
    cfv
    #
    cT
    cfv
    cC
    cur
    cfv
    #
    wceq
    #
    w3a
    cT
    @3
    @5
    cmhm
    co
    wcel
    @2
    @4
    @6
    @2
    cA
    crg
    wcel
    #
    @4
    @1
    @0
    cR
    crg
    wcel
    #
    @16
    cR
    crngring
    #
    cA
    cR
    cN
    mat2pmatbas.a
    matring
    sylan2
    cA
    @3
    @3
    eqid
    #
    ringmgp
    syl
    @2
    cC
    crg
    wcel
    #
    @6
    @1
    @0
    cP
    crg
    wcel
    #
    @20
    @1
    @17
    @21
    @18
    cP
    cR
    mat2pmatbas.p
    ply1ring
    syl
    cC
    cP
    cN
    mat2pmatbas.c
    matring
    sylan2
    cC
    @5
    @5
    eqid
    #
    ringmgp
    syl
    jca
    @2
    @7
    @12
    @15
    @1
    @0
    @17
    @7
    @18
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatf
    sylan2
    vx
    vy
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmatmul
    @1
    @0
    @17
    @15
    @18
    cA
    cB
    cC
    cP
    cR
    cT
    cH
    cN
    mat2pmatbas.t
    mat2pmatbas.a
    mat2pmatbas.b
    mat2pmatbas.p
    mat2pmatbas.c
    mat2pmatbas0.h
    mat2pmat1
    sylan2
    3jca
    vx
    vy
    cB
    cH
    @10
    @11
    @3
    @5
    cT
    @14
    @13
    cB
    cA
    @3
    @19
    mat2pmatbas.b
    mgpbas
    cH
    cC
    @5
    @22
    mat2pmatbas0.h
    mgpbas
    cA
    @10
    @3
    @19
    @10
    eqid
    mgpplusg
    cC
    @11
    @5
    @22
    @11
    eqid
    mgpplusg
    cA
    @13
    @3
    @19
    @13
    eqid
    ringidval
    cC
    @14
    @5
    @22
    @14
    eqid
    ringidval
    ismhm
    sylanbrc
end

include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "wa.mm"
include "crg.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "crngring.mm"
include "matring.mm"
include "sylan2.mm"
include "ply1ring.mm"
include "syl.mm"
include "jca.mm"
include "mat2pmatghm.mm"
include "mat2pmatmhm.mm"
include "eqid.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem mat2pmatrhm
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


  assert |- ( ( N e. Fin /\ R e. CRing ) -> T e. ( A RingHom C ) )

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
    crg
    wcel
    #
    cC
    crg
    wcel
    #
    wa
    cT
    cA
    cC
    cghm
    co
    wcel
    #
    cT
    cA
    cmgp
    cfv
    #
    cC
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    wa
    cT
    cA
    cC
    crh
    co
    wcel
    @2
    @3
    @4
    @1
    @0
    cR
    crg
    wcel
    #
    @3
    cR
    crngring
    #
    cA
    cR
    cN
    mat2pmatbas.a
    matring
    sylan2
    @1
    @0
    cP
    crg
    wcel
    #
    @4
    @1
    @9
    @11
    @10
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
    jca
    @2
    @5
    @8
    @1
    @0
    @9
    @5
    @10
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
    mat2pmatghm
    sylan2
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
    mat2pmatmhm
    jca
    cA
    cC
    cT
    @6
    @7
    @6
    eqid
    @7
    eqid
    isrhm
    sylanbrc
end

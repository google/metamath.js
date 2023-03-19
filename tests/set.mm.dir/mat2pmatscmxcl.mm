include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cn0.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "simpll.mm"
include "ply1ring.mm"
include "ad2antlr.mm"
include "cmgp.mm"
include "eqid.mm"
include "ply1moncl.mm"
include "ad2ant2l.mm"
include "w3a.mm"
include "simpl.mm"
include "anim2i.mm"
include "df-3an.mm"
include "sylibr.mm"
include "mat2pmatbas0.mm"
include "syl.mm"
include "matvscl.mm"
include "syl22anc.mm"

theorem mat2pmatscmxcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cT: class T
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  assume mat2pmatscmxcl.a: |- A = ( N Mat R )
  assume mat2pmatscmxcl.k: |- K = ( Base ` A )
  assume mat2pmatscmxcl.t: |- T = ( N matToPolyMat R )
  assume mat2pmatscmxcl.p: |- P = ( Poly1 ` R )
  assume mat2pmatscmxcl.c: |- C = ( N Mat P )
  assume mat2pmatscmxcl.b: |- B = ( Base ` C )
  assume mat2pmatscmxcl.m: |- .* = ( .s ` C )
  assume mat2pmatscmxcl.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume mat2pmatscmxcl.x: |- X = ( var1 ` R )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( M e. K /\ L e. NN0 ) ) -> ( ( L .^ X ) .* ( T ` M ) ) e. B )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cM
    cK
    wcel
    #
    cL
    cn0
    wcel
    #
    wa
    #
    wa
    #
    @0
    cP
    crg
    wcel
    #
    cL
    cX
    c.ex
    co
    #
    cP
    cbs
    cfv
    #
    wcel
    #
    cM
    cT
    cfv
    #
    cB
    wcel
    #
    @8
    @11
    c.as
    co
    cB
    wcel
    @0
    @1
    @5
    simpll
    @1
    @7
    @0
    @5
    cP
    cR
    mat2pmatscmxcl.p
    ply1ring
    ad2antlr
    @1
    @4
    @10
    @0
    @3
    @9
    cL
    cP
    cR
    c.ex
    cP
    cmgp
    cfv
    #
    cX
    mat2pmatscmxcl.p
    mat2pmatscmxcl.x
    @13
    eqid
    mat2pmatscmxcl.e
    @9
    eqid
    #
    ply1moncl
    ad2ant2l
    @6
    @0
    @1
    @3
    w3a
    #
    @12
    @6
    @2
    @3
    wa
    @15
    @5
    @3
    @2
    @3
    @4
    simpl
    anim2i
    @0
    @1
    @3
    df-3an
    sylibr
    cA
    cK
    cC
    cP
    cR
    cT
    cB
    cM
    cN
    mat2pmatscmxcl.t
    mat2pmatscmxcl.a
    mat2pmatscmxcl.k
    mat2pmatscmxcl.p
    mat2pmatscmxcl.c
    mat2pmatscmxcl.b
    mat2pmatbas0
    syl
    cC
    cB
    @8
    cP
    c.as
    @9
    cN
    @11
    @14
    mat2pmatscmxcl.c
    mat2pmatscmxcl.b
    mat2pmatscmxcl.m
    matvscl
    syl22anc
end

include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cgrp.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "pmatring.mm"
include "3adant3.mm"
include "ringgrp.mm"
include "syl.mm"
include "chpdmatlem0.mm"
include "mat2pmatbas.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"

theorem chpdmatlem1
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.1: class .1.
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume chpdmat.c: |- C = ( N CharPlyMat R )
  assume chpdmat.p: |- P = ( Poly1 ` R )
  assume chpdmat.a: |- A = ( N Mat R )
  assume chpdmat.s: |- S = ( algSc ` P )
  assume chpdmat.b: |- B = ( Base ` A )
  assume chpdmat.x: |- X = ( var1 ` R )
  assume chpdmat.0: |- .0. = ( 0g ` R )
  assume chpdmat.g: |- G = ( mulGrp ` P )
  assume chpdmat.m: |- .- = ( -g ` P )
  assume chpdmatlem.q: |- Q = ( N Mat P )
  assume chpdmatlem.1: |- .1. = ( 1r ` Q )
  assume chpdmatlem.m: |- .x. = ( .s ` Q )
  assume chpdmatlem.z: |- Z = ( -g ` Q )
  assume chpdmatlem.t: |- T = ( N matToPolyMat R )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( ( X .x. .1. ) Z ( T ` M ) ) e. ( Base ` Q ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cQ
    cgrp
    wcel
    #
    cX
    c.1
    c.x
    co
    #
    cQ
    cbs
    cfv
    #
    wcel
    #
    cM
    cT
    cfv
    #
    @6
    wcel
    @5
    @8
    cZ
    co
    @6
    wcel
    @3
    cQ
    crg
    wcel
    #
    @4
    @0
    @1
    @9
    @2
    cQ
    cP
    cR
    cN
    chpdmat.p
    chpdmatlem.q
    pmatring
    3adant3
    cQ
    ringgrp
    syl
    @0
    @1
    @7
    @2
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    c.x
    c.1
    cG
    c.mi
    cN
    cX
    c.0
    chpdmat.c
    chpdmat.p
    chpdmat.a
    chpdmat.s
    chpdmat.b
    chpdmat.x
    chpdmat.0
    chpdmat.g
    chpdmat.m
    chpdmatlem.q
    chpdmatlem.1
    chpdmatlem.m
    chpdmatlem0
    3adant3
    cA
    cB
    cQ
    cP
    cR
    cT
    cM
    cN
    chpdmatlem.t
    chpdmat.a
    chpdmat.b
    chpdmat.p
    chpdmatlem.q
    mat2pmatbas
    @6
    cQ
    cZ
    @5
    @8
    @6
    eqid
    chpdmatlem.z
    grpsubcl
    syl3anc
end

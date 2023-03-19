include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cbs.mm"
include "cgrp.mm"
include "wa.mm"
include "pmatring.mm"
include "ringgrp.mm"
include "syl.mm"
include "3adant3.mm"
include "ply1ring.mm"
include "anim2i.mm"
include "eqid.mm"
include "vr1cl.mm"
include "3ad2ant2.mm"
include "ringidcl.mm"
include "matvscl.mm"
include "syl12anc.mm"
include "mat2pmatbas.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"

theorem chmatcl
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let c.x: class .x.
  let c.1: class .1.
  let cH: class H
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume chmatcl.a: |- A = ( N Mat R )
  assume chmatcl.b: |- B = ( Base ` A )
  assume chmatcl.p: |- P = ( Poly1 ` R )
  assume chmatcl.y: |- Y = ( N Mat P )
  assume chmatcl.x: |- X = ( var1 ` R )
  assume chmatcl.t: |- T = ( N matToPolyMat R )
  assume chmatcl.s: |- .- = ( -g ` Y )
  assume chmatcl.m: |- .x. = ( .s ` Y )
  assume chmatcl.1: |- .1. = ( 1r ` Y )
  assume chmatcl.h: |- H = ( ( X .x. .1. ) .- ( T ` M ) )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> H e. ( Base ` Y ) )

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
    cH
    cX
    c.1
    c.x
    co
    #
    cM
    cT
    cfv
    #
    c.mi
    co
    #
    cY
    cbs
    cfv
    #
    chmatcl.h
    @3
    cY
    cgrp
    wcel
    #
    @4
    @7
    wcel
    #
    @5
    @7
    wcel
    @6
    @7
    wcel
    @0
    @1
    @8
    @2
    @0
    @1
    wa
    cY
    crg
    wcel
    #
    @8
    cY
    cP
    cR
    cN
    chmatcl.p
    chmatcl.y
    pmatring
    #
    cY
    ringgrp
    syl
    3adant3
    @3
    @0
    cP
    crg
    wcel
    #
    wa
    #
    cX
    cP
    cbs
    cfv
    #
    wcel
    #
    c.1
    @7
    wcel
    #
    @9
    @0
    @1
    @13
    @2
    @1
    @12
    @0
    cP
    cR
    chmatcl.p
    ply1ring
    anim2i
    3adant3
    @1
    @0
    @15
    @2
    @14
    cP
    cR
    cX
    chmatcl.x
    chmatcl.p
    @14
    eqid
    #
    vr1cl
    3ad2ant2
    @3
    @10
    @16
    @0
    @1
    @10
    @2
    @11
    3adant3
    @7
    cY
    c.1
    @7
    eqid
    #
    chmatcl.1
    ringidcl
    syl
    cY
    @7
    cX
    cP
    c.x
    @14
    cN
    c.1
    @17
    chmatcl.y
    @18
    chmatcl.m
    matvscl
    syl12anc
    cA
    cB
    cY
    cP
    cR
    cT
    cM
    cN
    chmatcl.t
    chmatcl.a
    chmatcl.b
    chmatcl.p
    chmatcl.y
    mat2pmatbas
    @7
    cY
    c.mi
    @4
    @5
    @18
    chmatcl.s
    grpsubcl
    syl3anc
    syl5eqel
end

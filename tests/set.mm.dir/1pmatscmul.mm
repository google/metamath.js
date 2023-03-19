include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "ply1ring.mm"
include "anim2i.mm"
include "3adant3.mm"
include "simp3.mm"
include "pmatring.mm"
include "ringidcl.mm"
include "syl.mm"
include "matvscl.mm"
include "syl12anc.mm"

theorem 1pmatscmul
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
  let cE: class E
  let c.as: class .*
  let cN: class N
  assume 1pmatscmul.p: |- P = ( Poly1 ` R )
  assume 1pmatscmul.c: |- C = ( N Mat P )
  assume 1pmatscmul.b: |- B = ( Base ` C )
  assume 1pmatscmul.e: |- E = ( Base ` P )
  assume 1pmatscmul.m: |- .* = ( .s ` C )
  assume 1pmatscmul.1: |- .1. = ( 1r ` C )


  assert |- ( ( N e. Fin /\ R e. Ring /\ Q e. E ) -> ( Q .* .1. ) e. B )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cQ
    cE
    wcel
    #
    w3a
    #
    @0
    cP
    crg
    wcel
    #
    wa
    #
    @2
    c.1
    cB
    wcel
    #
    cQ
    c.1
    c.as
    co
    cB
    wcel
    @0
    @1
    @5
    @2
    @1
    @4
    @0
    cP
    cR
    1pmatscmul.p
    ply1ring
    anim2i
    3adant3
    @0
    @1
    @2
    simp3
    @3
    cC
    crg
    wcel
    #
    @6
    @0
    @1
    @7
    @2
    cC
    cP
    cR
    cN
    1pmatscmul.p
    1pmatscmul.c
    pmatring
    3adant3
    cB
    cC
    c.1
    1pmatscmul.b
    1pmatscmul.1
    ringidcl
    syl
    cC
    cB
    cQ
    cP
    c.as
    cE
    cN
    c.1
    1pmatscmul.e
    1pmatscmul.c
    1pmatscmul.b
    1pmatscmul.m
    matvscl
    syl12anc
end

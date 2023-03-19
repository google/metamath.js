include "cfn.mm"
include "wcel.mm"
include "ccrg.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crg.mm"
include "wa.mm"
include "crngring.mm"
include "ply1ring.mm"
include "syl.mm"
include "anim2i.mm"
include "3adant3.mm"
include "chpmatply1.mm"
include "pmatring.mm"
include "sylan2.mm"
include "ringidcl.mm"
include "matvscl.mm"
include "syl12anc.mm"
include "wi.mm"
include "risset.mm"
include "oveq1.mm"
include "eqcoms.mm"
include "a1i.mm"
include "reximdva.mm"
include "com12.mm"
include "sylbi.mm"
include "mpcom.mm"
include "wb.mm"
include "scmatel.mm"
include "mpbir2and.mm"

theorem chmaidscmat
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cE: class E
  let cK: class K
  let cM: class M
  let cN: class N
  let cY: class Y
  let c.0: class .0.
  let vc: setvar c
  assume chmaidscmat.a: |- A = ( N Mat R )
  assume chmaidscmat.b: |- B = ( Base ` A )
  assume chmaidscmat.c: |- C = ( N CharPlyMat R )
  assume chmaidscmat.p: |- P = ( Poly1 ` R )
  assume chmaidscmat.e: |- E = ( Base ` P )
  assume chmaidscmat.y: |- Y = ( N Mat P )
  assume chmaidscmat.k: |- K = ( Base ` Y )
  assume chmaidscmat.m: |- .x. = ( .s ` Y )
  assume chmaidscmat.0: |- .0. = ( 0g ` P )
  assume chmaidscmat.1: |- .1. = ( 1r ` Y )
  assume chmaidscmat.d: |- S = ( N ScMat P )


  assert |- ( ( N e. Fin /\ R e. CRing /\ M e. B ) -> ( ( C ` M ) .x. .1. ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    ccrg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cM
    cC
    cfv
    #
    c.1
    c.x
    co
    #
    cS
    wcel
    #
    @5
    cK
    wcel
    #
    @5
    vc
    cv
    #
    c.1
    c.x
    co
    wceq
    #
    vc
    cE
    wrex
    #
    @3
    @0
    cP
    crg
    wcel
    #
    wa
    #
    @4
    cE
    wcel
    #
    c.1
    cK
    wcel
    #
    @7
    @0
    @1
    @12
    @2
    @1
    @11
    @0
    @1
    cR
    crg
    wcel
    #
    @11
    cR
    crngring
    #
    cP
    cR
    chmaidscmat.p
    ply1ring
    syl
    anim2i
    3adant3
    #
    cA
    cB
    cC
    cP
    cR
    cE
    cM
    cN
    chmaidscmat.c
    chmaidscmat.a
    chmaidscmat.b
    chmaidscmat.p
    chmaidscmat.e
    chpmatply1
    #
    @0
    @1
    @14
    @2
    @0
    @1
    wa
    cY
    crg
    wcel
    #
    @14
    @1
    @0
    @15
    @19
    @16
    cY
    cP
    cR
    cN
    chmaidscmat.p
    chmaidscmat.y
    pmatring
    sylan2
    cK
    cY
    c.1
    chmaidscmat.k
    chmaidscmat.1
    ringidcl
    syl
    3adant3
    cY
    cK
    @4
    cP
    c.x
    cE
    cN
    c.1
    chmaidscmat.e
    chmaidscmat.y
    chmaidscmat.k
    chmaidscmat.m
    matvscl
    syl12anc
    @13
    @3
    @10
    @18
    @13
    @8
    @4
    wceq
    #
    vc
    cE
    wrex
    #
    @3
    @10
    wi
    vc
    @4
    cE
    risset
    @3
    @21
    @10
    @3
    @20
    @9
    vc
    cE
    @20
    @9
    wi
    @3
    @8
    cE
    wcel
    wa
    @9
    @4
    @8
    @4
    @8
    c.1
    c.x
    oveq1
    eqcoms
    a1i
    reximdva
    com12
    sylbi
    mpcom
    @3
    @12
    @6
    @7
    @10
    wa
    wb
    @17
    cY
    cK
    cP
    cS
    c.x
    c.1
    cE
    @5
    cN
    crg
    vc
    chmaidscmat.e
    chmaidscmat.y
    chmaidscmat.k
    chmaidscmat.1
    chmaidscmat.m
    chmaidscmat.d
    scmatel
    syl
    mpbir2and
end

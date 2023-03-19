include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cdecpmat.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cn0.mm"
include "ovexd.mm"
include "oveq2.mm"
include "decpmataa0.mm"
include "mptnn0fsuppd.mm"

theorem decpmatfsupp
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cK: class K
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vx: setvar x
  assume decpmate.p: |- P = ( Poly1 ` R )
  assume decpmate.c: |- C = ( N Mat P )
  assume decpmate.b: |- B = ( Base ` C )
  assume decpmatcl.a: |- A = ( N Mat R )
  assume decpmatfsupp.0: |- .0. = ( 0g ` A )

  disjoint B k
  disjoint M k
  disjoint R k
  disjoint B i
  disjoint B j
  disjoint i j
  disjoint K i
  disjoint K j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  disjoint V i
  disjoint V j
  disjoint B a
  disjoint B b
  disjoint B s
  disjoint B x
  disjoint a b
  disjoint a k
  disjoint a s
  disjoint a x
  disjoint b k
  disjoint b s
  disjoint b x
  disjoint k s
  disjoint k x
  disjoint s x
  disjoint M a
  disjoint M b
  disjoint M s
  disjoint M x
  disjoint N a
  disjoint N b
  disjoint N s
  disjoint N x
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint i s
  disjoint i x
  disjoint j s
  disjoint j x
  disjoint R a
  disjoint R b
  disjoint R s
  disjoint R x
  disjoint .0. i
  disjoint .0. j
  disjoint .0. s
  disjoint .0. x
  assert |- ( ( R e. Ring /\ M e. B ) -> ( k e. NN0 |-> ( M decompPMat k ) ) finSupp .0. )

  proof
    cR
    crg
    wcel
    cM
    cB
    wcel
    wa
    #
    vx
    cvv
    cM
    vk
    cv
    #
    cdecpmat
    co
    cM
    vx
    cv
    #
    cdecpmat
    co
    vk
    cvv
    c.0
    vs
    c.0
    cvv
    wcel
    @0
    c.0
    cA
    c0g
    cfv
    cvv
    decpmatfsupp.0
    cA
    c0g
    fvex
    eqeltri
    a1i
    @0
    @1
    cn0
    wcel
    wa
    cM
    @1
    cdecpmat
    ovexd
    @1
    @2
    cM
    cdecpmat
    oveq2
    vx
    cA
    cB
    cC
    cP
    cR
    cM
    cN
    c.0
    vs
    decpmate.p
    decpmate.c
    decpmate.b
    decpmatcl.a
    decpmatfsupp.0
    decpmataa0
    mptnn0fsuppd
end

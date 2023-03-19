include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "ianor.mm"
include "mpt2ndm0.mm"
include "oveqd.mm"
include "0ov.mm"
include "syl6eq.mm"
include "notnotb.mm"
include "cmpt2.mm"
include "adantr.mm"
include "eqid.mm"
include "adantl.mm"
include "eqtrd.mm"
include "sylanbr.mm"
include "jaoi3.mm"
include "sylbi.mm"

theorem 2mpt20
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let cE: class E
  let cF: class F
  let cO: class O
  let cX: class X
  let cY: class Y
  let vs: setvar s
  assume 2mpt20.o: |- O = ( x e. A , y e. B |-> E )
  assume 2mpt20.u: |- ( ( X e. A /\ Y e. B ) -> ( X O Y ) = ( s e. C , t e. D |-> F ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C s
  disjoint C t
  disjoint s t
  disjoint D s
  disjoint D t
  assert |- ( -. ( ( X e. A /\ Y e. B ) /\ ( S e. C /\ T e. D ) ) -> ( S ( X O Y ) T ) = (/) )

  proof
    cX
    cA
    wcel
    cY
    cB
    wcel
    wa
    #
    cS
    cC
    wcel
    cT
    cD
    wcel
    wa
    #
    wa
    wn
    @0
    wn
    #
    @1
    wn
    #
    wo
    cS
    cT
    cX
    cY
    cO
    co
    #
    co
    #
    c0
    wceq
    #
    @0
    @1
    ianor
    @2
    @6
    @3
    @2
    @5
    cS
    cT
    c0
    co
    c0
    @2
    @4
    c0
    cS
    cT
    vx
    vy
    cE
    cO
    cX
    cY
    cA
    cB
    2mpt20.o
    mpt2ndm0
    oveqd
    cS
    cT
    0ov
    syl6eq
    @2
    wn
    @0
    @3
    @6
    @0
    notnotb
    @0
    @3
    wa
    #
    @5
    cS
    cT
    vs
    vt
    cC
    cD
    cF
    cmpt2
    #
    co
    #
    c0
    @7
    @4
    @8
    cS
    cT
    @0
    @4
    @8
    wceq
    @3
    2mpt20.u
    adantr
    oveqd
    @3
    @9
    c0
    wceq
    @0
    vs
    vt
    cF
    @8
    cS
    cT
    cC
    cD
    @8
    eqid
    mpt2ndm0
    adantl
    eqtrd
    sylanbr
    jaoi3
    sylbi
end

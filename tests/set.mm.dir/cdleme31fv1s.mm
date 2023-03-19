include "wcel.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "eqid.mm"
include "cdleme31fv1.mm"
include "cdleme31so.mm"
include "adantr.mm"
include "eqtr4d.mm"

theorem cdleme31fv1s
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cF: class F
  let c.or: class .\/
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let vs: setvar s
  let cC: class C
  assume cdleme31.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme31.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

  disjoint B x
  disjoint .<_ x
  disjoint P x
  disjoint Q x
  disjoint W x
  disjoint s x
  disjoint s z
  disjoint X s
  disjoint x z
  disjoint X x
  disjoint X z
  disjoint A x
  disjoint B s
  disjoint B z
  disjoint .\/ x
  disjoint ./\ x
  disjoint N x
  disjoint C x
  assert |- ( ( X e. B /\ ( P =/= Q /\ -. X .<_ W ) ) -> ( F ` X ) = [_ X / x ]_ O )

  proof
    cX
    cB
    wcel
    #
    cP
    cQ
    wne
    cX
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    cX
    cF
    cfv
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @2
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    wa
    vz
    cv
    cN
    @3
    c.or
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    #
    vx
    cX
    cO
    csb
    #
    vx
    vz
    cA
    cB
    @4
    cP
    cQ
    cF
    c.or
    c.le
    c.an
    cN
    cO
    cW
    cX
    vs
    cdleme31.o
    cdleme31.f
    @4
    eqid
    #
    cdleme31fv1
    @0
    @5
    @4
    wceq
    @1
    vx
    vz
    cA
    cB
    @4
    c.or
    c.le
    c.an
    cN
    cO
    cW
    cX
    vs
    cdleme31.o
    @6
    cdleme31so
    adantr
    eqtr4d
end

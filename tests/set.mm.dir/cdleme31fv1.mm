include "wcel.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "cif.mm"
include "cdleme31fv.mm"
include "iftrue.mm"
include "sylan9eq.mm"

theorem cdleme31fv1
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume cdleme31.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme31.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )
  assume cdleme31.c: |- C = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( X ./\ W ) ) = X ) -> z = ( N .\/ ( X ./\ W ) ) ) )

  disjoint B x
  disjoint C x
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
  assert |- ( ( X e. B /\ ( P =/= Q /\ -. X .<_ W ) ) -> ( F ` X ) = C )

  proof
    cX
    cB
    wcel
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
    cX
    cF
    cfv
    @0
    cC
    cX
    cif
    cC
    vx
    vz
    cA
    cB
    cC
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
    cdleme31.c
    cdleme31fv
    @0
    cC
    cX
    iftrue
    sylan9eq
end

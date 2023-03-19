include "wceq.mm"
include "wcel.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "simpl.mm"
include "necon2bi.mm"
include "cdleme31fv2.mm"
include "sylan2.mm"

theorem cdleme31id
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cF: class F
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let cX: class X
  assume cdleme31fv2.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

  disjoint B x
  disjoint .<_ x
  disjoint P x
  disjoint Q x
  disjoint W x
  disjoint X x
  assert |- ( ( X e. B /\ P = Q ) -> ( F ` X ) = X )

  proof
    cP
    cQ
    wceq
    cX
    cB
    wcel
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wn
    cX
    cF
    cfv
    cX
    wceq
    @2
    cP
    cQ
    @0
    @1
    simpl
    necon2bi
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    cX
    cdleme31fv2.f
    cdleme31fv2
    sylan2
end

include "wcel.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi2d.mm"
include "biimparc.mm"
include "adantll.mm"
include "iffalsed.mm"
include "simpr.mm"
include "eqtrd.mm"
include "simpl.mm"
include "fvmptd.mm"

theorem cdleme31fv2
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
  assert |- ( ( X e. B /\ -. ( P =/= Q /\ -. X .<_ W ) ) -> ( F ` X ) = X )

  proof
    cX
    cB
    wcel
    #
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wn
    #
    wa
    #
    vx
    cX
    @1
    vx
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cO
    @7
    cif
    #
    cX
    cB
    cF
    cB
    cF
    vx
    cB
    @11
    cmpt
    wceq
    @6
    cdleme31fv2.f
    a1i
    @6
    @7
    cX
    wceq
    #
    wa
    #
    @11
    @7
    cX
    @13
    @10
    cO
    @7
    @5
    @12
    @10
    wn
    #
    @0
    @12
    @14
    @5
    @12
    @10
    @4
    @12
    @9
    @3
    @1
    @12
    @8
    @2
    @7
    cX
    cW
    c.le
    breq1
    notbid
    anbi2d
    notbid
    biimparc
    adantll
    iffalsed
    @6
    @12
    simpr
    eqtrd
    @0
    @5
    simpl
    #
    @15
    fvmptd
end

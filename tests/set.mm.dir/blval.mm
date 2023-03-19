include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cbl.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "blfval.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "simprl.mm"
include "oveq1d.mm"
include "simprr.mm"
include "breq12d.mm"
include "rabbidv.mm"
include "simp2.mm"
include "simp3.mm"
include "cdm.mm"
include "elfvdm.mm"
include "rabexg.mm"
include "syl.mm"
include "ovmpt2d.mm"

theorem blval
  let vx: setvar x
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let cA: class A
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph
  let cQ: class Q
  let cS: class S

  disjoint P x
  disjoint D x
  disjoint R x
  disjoint X x
  disjoint A x
  disjoint r x
  disjoint r y
  disjoint P r
  disjoint x y
  disjoint P y
  disjoint ph x
  disjoint Q x
  disjoint S x
  disjoint D r
  disjoint D y
  disjoint R r
  disjoint R y
  disjoint X r
  disjoint X y
  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( P ( ball ` D ) R ) = { x e. X | ( P D x ) < R } )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    w3a
    #
    vy
    vr
    cP
    cR
    cX
    cxr
    vy
    cv
    #
    vx
    cv
    #
    cD
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    vx
    cX
    crab
    #
    cP
    @5
    cD
    co
    #
    cR
    clt
    wbr
    #
    vx
    cX
    crab
    #
    cD
    cbl
    cfv
    #
    cvv
    @0
    @1
    @13
    vy
    vr
    cX
    cxr
    @9
    cmpt2
    wceq
    @2
    vy
    vx
    cD
    cX
    vr
    blfval
    3ad2ant1
    @3
    @4
    cP
    wceq
    #
    @7
    cR
    wceq
    #
    wa
    wa
    #
    @8
    @11
    vx
    cX
    @16
    @6
    @10
    @7
    cR
    clt
    @16
    @4
    cP
    @5
    cD
    @3
    @14
    @15
    simprl
    oveq1d
    @3
    @14
    @15
    simprr
    breq12d
    rabbidv
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @3
    cX
    cxmt
    cdm
    #
    wcel
    #
    @12
    cvv
    wcel
    @0
    @1
    @18
    @2
    cD
    cX
    cxmt
    elfvdm
    3ad2ant1
    @11
    vx
    cX
    @17
    rabexg
    syl
    ovmpt2d
end

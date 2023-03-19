include "wnel.mm"
include "csb.mm"
include "wo.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "df-nel.mm"
include "orbi12i.mm"
include "ianor.mm"
include "bitr4i.mm"
include "cv.mm"
include "wex.mm"
include "neq0.mm"
include "mpt2xeldm.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "con1i.mm"

theorem mpt2xneldm
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cX: class X
  let cY: class Y
  let vn: setvar n
  assume mpt2xeldm2.f: |- F = ( x e. C , y e. D |-> R )

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint D y
  disjoint X x
  disjoint Y x
  disjoint C n
  disjoint D n
  disjoint F n
  disjoint X n
  disjoint n x
  disjoint Y n
  assert |- ( ( X e/ C \/ Y e/ [_ X / x ]_ D ) -> ( X F Y ) = (/) )

  proof
    cX
    cC
    wnel
    #
    cY
    vx
    cX
    cD
    csb
    #
    wnel
    #
    wo
    #
    cX
    cC
    wcel
    #
    cY
    @1
    wcel
    #
    wa
    #
    wn
    #
    cX
    cY
    cF
    co
    #
    c0
    wceq
    #
    @3
    @4
    wn
    #
    @5
    wn
    #
    wo
    @7
    @0
    @10
    @2
    @11
    cX
    cC
    df-nel
    cY
    @1
    df-nel
    orbi12i
    @4
    @5
    ianor
    bitr4i
    @9
    @6
    @9
    wn
    vn
    cv
    #
    @8
    wcel
    #
    vn
    wex
    @6
    vn
    @8
    neq0
    @13
    @6
    vn
    vx
    vy
    cC
    cD
    cR
    cF
    @12
    cX
    cY
    mpt2xeldm2.f
    mpt2xeldm
    exlimiv
    sylbi
    con1i
    sylbi
end

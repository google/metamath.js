include "cdm.mm"
include "cxp.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "coprab.mm"
include "cmpt2.mm"
include "df-mpt2.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmoprabss.mm"
include "eqsstri.mm"
include "nssdmovg.mm"
include "mpan.mm"

theorem mpt2ndm0
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume mpt2ndm0.f: |- F = ( x e. X , y e. Y |-> C )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint Y z
  disjoint C z
  assert |- ( -. ( V e. X /\ W e. Y ) -> ( V F W ) = (/) )

  proof
    cF
    cdm
    #
    cX
    cY
    cxp
    #
    wss
    cV
    cX
    wcel
    cW
    cY
    wcel
    wa
    wn
    cV
    cW
    cF
    co
    c0
    wceq
    @0
    vx
    cv
    cX
    wcel
    vy
    cv
    cY
    wcel
    wa
    vz
    cv
    cC
    wceq
    #
    wa
    vx
    vy
    vz
    coprab
    #
    cdm
    @1
    cF
    @3
    cF
    vx
    vy
    cX
    cY
    cC
    cmpt2
    @3
    mpt2ndm0.f
    vx
    vy
    vz
    cX
    cY
    cC
    df-mpt2
    eqtri
    dmeqi
    @2
    vx
    vy
    vz
    cX
    cY
    dmoprabss
    eqsstri
    cV
    cW
    cX
    cY
    cF
    nssdmovg
    mpan
end

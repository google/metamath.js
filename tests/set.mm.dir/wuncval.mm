include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "cwun.mm"
include "crab.mm"
include "cint.mm"
include "cwunm.mm"
include "cfv.mm"
include "wceq.mm"
include "elex.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "wunex.mm"
include "rabn0.mm"
include "sylibr.mm"
include "intex.mm"
include "sylib.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "df-wunc.mm"
include "fvmptg.mm"
include "syl2anc.mm"

theorem wuncval
  let vu: setvar u
  let cA: class A
  let cV: class V
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cU: class U
  let cF: class F

  disjoint A u
  disjoint V u
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint U u
  disjoint V m
  disjoint V n
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint F m
  disjoint F n
  disjoint F u
  disjoint F v
  disjoint F w
  assert |- ( A e. V -> ( wUniCl ` A ) = |^| { u e. WUni | A C_ u } )

  proof
    cA
    cV
    wcel
    #
    cA
    cvv
    wcel
    cA
    vu
    cv
    #
    wss
    #
    vu
    cwun
    crab
    #
    cint
    #
    cvv
    wcel
    #
    cA
    cwunm
    cfv
    @4
    wceq
    cA
    cV
    elex
    @0
    @3
    c0
    wne
    #
    @5
    @0
    @2
    vu
    cwun
    wrex
    @6
    vu
    cA
    cV
    wunex
    @2
    vu
    cwun
    rabn0
    sylibr
    @3
    intex
    sylib
    vx
    cA
    vx
    cv
    #
    @1
    wss
    #
    vu
    cwun
    crab
    #
    cint
    @4
    cvv
    cvv
    cwunm
    @7
    cA
    wceq
    #
    @9
    @3
    @10
    @8
    @2
    vu
    cwun
    @7
    cA
    @1
    sseq1
    rabbidv
    inteqd
    vx
    vu
    df-wunc
    fvmptg
    syl2anc
end

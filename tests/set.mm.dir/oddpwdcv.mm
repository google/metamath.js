include "cn0.mm"
include "cxp.mm"
include "wcel.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmul.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "wceq.mm"
include "df-ov.mm"
include "a1i.mm"
include "wa.mm"
include "elxp6.mm"
include "simprbi.mm"
include "cv.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "syl.mm"
include "3eqtr2d.mm"

theorem oddpwdcv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cJ: class J
  let cW: class W
  let va: setvar a
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  assume oddpwdc.j: |- J = { z e. NN | -. 2 || z }
  assume oddpwdc.f: |- F = ( x e. J , y e. NN0 |-> ( ( 2 ^ y ) x. x ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J x
  disjoint J y
  disjoint W x
  disjoint W y
  disjoint a k
  disjoint a l
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint k l
  disjoint k m
  disjoint k n
  disjoint k o
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint l m
  disjoint l n
  disjoint l o
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint m n
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint F a
  disjoint J a
  assert |- ( W e. ( J X. NN0 ) -> ( F ` W ) = ( ( 2 ^ ( 2nd ` W ) ) x. ( 1st ` W ) ) )

  proof
    cW
    cJ
    cn0
    cxp
    wcel
    #
    cW
    cF
    cfv
    cW
    c1st
    cfv
    #
    cW
    c2nd
    cfv
    #
    cop
    #
    cF
    cfv
    #
    @1
    @2
    cF
    co
    #
    c2
    @2
    cexp
    co
    #
    @1
    cmul
    co
    #
    @0
    cW
    @3
    cF
    cW
    cJ
    cn0
    1st2nd2
    fveq2d
    @5
    @4
    wceq
    @0
    @1
    @2
    cF
    df-ov
    a1i
    @0
    @1
    cJ
    wcel
    @2
    cn0
    wcel
    wa
    #
    @5
    @7
    wceq
    @0
    cW
    @3
    wceq
    @8
    cW
    cJ
    cn0
    elxp6
    simprbi
    vx
    vy
    @1
    @2
    cJ
    cn0
    c2
    vy
    cv
    #
    cexp
    co
    #
    vx
    cv
    #
    cmul
    co
    @7
    cF
    @10
    @1
    cmul
    co
    @11
    @1
    @10
    cmul
    oveq2
    @9
    @2
    wceq
    @10
    @6
    @1
    cmul
    @9
    @2
    c2
    cexp
    oveq2
    oveq1d
    oddpwdc.f
    @6
    @1
    cmul
    ovex
    ovmpt2
    syl
    3eqtr2d
end

include "cn0.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cab.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "cbvabv.mm"
include "4sqlem19.mm"
include "4sqlem2.mm"

theorem 4sq
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint A b
  disjoint c d
  disjoint A c
  disjoint A d
  disjoint a m
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b m
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c m
  disjoint c n
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d m
  disjoint d n
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. NN0 <-> E. a e. ZZ E. b e. ZZ E. c e. ZZ E. d e. ZZ A = ( ( ( a ^ 2 ) + ( b ^ 2 ) ) + ( ( c ^ 2 ) + ( d ^ 2 ) ) ) )

  proof
    vx
    vy
    vz
    vw
    cA
    cn0
    vm
    va
    vb
    vc
    vd
    vx
    vy
    vz
    vw
    vm
    cv
    #
    vx
    cv
    c2
    cexp
    co
    vy
    cv
    c2
    cexp
    co
    caddc
    co
    vz
    cv
    c2
    cexp
    co
    vw
    cv
    c2
    cexp
    co
    caddc
    co
    caddc
    co
    #
    wceq
    #
    vw
    cz
    wrex
    vz
    cz
    wrex
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    vm
    cab
    vn
    @4
    vn
    cv
    #
    @1
    wceq
    #
    vw
    cz
    wrex
    vz
    cz
    wrex
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    vm
    vn
    @0
    @5
    wceq
    #
    @3
    @7
    vx
    vy
    cz
    cz
    @8
    @2
    @6
    vz
    vw
    cz
    cz
    @0
    @5
    @1
    eqeq1
    2rexbidv
    2rexbidv
    cbvabv
    4sqlem19
    4sqlem2
end

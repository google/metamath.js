include "cha.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "ctop.mm"
include "ishaus.mm"
include "simprbi.mm"
include "neeq1.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "neeq2.mm"
include "3anbi2d.mm"
include "rspc2v.mm"
include "syl5.mm"
include "ex.mm"
include "com3r.mm"
include "3imp2.mm"

theorem hausnei
  let cP: class P
  let cQ: class Q
  let vm: setvar m
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vj: setvar j
  assume ist0.1: |- X = U. J

  disjoint m n
  disjoint J m
  disjoint J n
  disjoint P m
  disjoint P n
  disjoint Q m
  disjoint Q n
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint A o
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B o
  disjoint B x
  disjoint B z
  disjoint a j
  disjoint a m
  disjoint a n
  disjoint a o
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint J a
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m o
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n o
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint J o
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint X j
  disjoint X o
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint P x
  disjoint P y
  disjoint Q y
  assert |- ( ( J e. Haus /\ ( P e. X /\ Q e. X /\ P =/= Q ) ) -> E. n e. J E. m e. J ( P e. n /\ Q e. m /\ ( n i^i m ) = (/) ) )

  proof
    cJ
    cha
    wcel
    #
    cP
    cX
    wcel
    #
    cQ
    cX
    wcel
    #
    cP
    cQ
    wne
    #
    cP
    vn
    cv
    #
    wcel
    #
    cQ
    vm
    cv
    #
    wcel
    #
    @4
    @6
    cin
    c0
    wceq
    #
    w3a
    #
    vm
    cJ
    wrex
    vn
    cJ
    wrex
    #
    @1
    @2
    @0
    @3
    @10
    wi
    #
    @1
    @2
    @0
    @11
    wi
    @0
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @12
    @4
    wcel
    #
    @13
    @6
    wcel
    #
    @8
    w3a
    #
    vm
    cJ
    wrex
    vn
    cJ
    wrex
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    wa
    @11
    @0
    cJ
    ctop
    wcel
    @20
    vx
    vy
    vm
    vn
    cJ
    cX
    ist0.1
    ishaus
    simprbi
    @19
    @11
    cP
    @13
    wne
    #
    @5
    @16
    @8
    w3a
    #
    vm
    cJ
    wrex
    vn
    cJ
    wrex
    #
    wi
    vx
    vy
    cP
    cQ
    cX
    cX
    @12
    cP
    wceq
    #
    @14
    @21
    @18
    @23
    @12
    cP
    @13
    neeq1
    @24
    @17
    @22
    vn
    vm
    cJ
    cJ
    @24
    @15
    @5
    @16
    @8
    @12
    cP
    @4
    eleq1
    3anbi1d
    2rexbidv
    imbi12d
    @13
    cQ
    wceq
    #
    @21
    @3
    @23
    @10
    @13
    cQ
    cP
    neeq2
    @25
    @22
    @9
    vn
    vm
    cJ
    cJ
    @25
    @16
    @7
    @5
    @8
    @13
    cQ
    @6
    eleq1
    3anbi2d
    2rexbidv
    imbi12d
    rspc2v
    syl5
    ex
    com3r
    3imp2
end

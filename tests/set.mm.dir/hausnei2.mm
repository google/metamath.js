include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cha.mm"
include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "cnei.mm"
include "ishaus2.mm"
include "ctop.mm"
include "wb.mm"
include "topontop.mm"
include "wa.mm"
include "simp1.mm"
include "adantr.mm"
include "simp2.mm"
include "adantl.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "simp3.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "ineq2.mm"
include "rspc2ev.mm"
include "ex.mm"
include "3expib.mm"
include "rexlimdvv.mm"
include "wss.mm"
include "neii2.mm"
include "vex.mm"
include "snss.mm"
include "anbi1i.mm"
include "simp1l.mm"
include "simp2l.mm"
include "ss2in.mm"
include "ssn0.mm"
include "necon4d.mm"
include "syl.mm"
include "ad2ant2l.mm"
include "3impia.mm"
include "3jca.mm"
include "3exp.mm"
include "syl5bir.mm"
include "com3r.mm"
include "imp.mm"
include "3adant1.mm"
include "reximdv.mm"
include "com34.mm"
include "3imp.mm"
include "com24.mm"
include "impd.mm"
include "syl2and.mm"
include "impbid.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "bitrd.mm"

theorem hausnei2
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cY: class Y

  disjoint x y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J y
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint u w
  disjoint K u
  disjoint v w
  disjoint K v
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint w z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c m
  disjoint c n
  disjoint c o
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint J c
  disjoint d f
  disjoint d g
  disjoint d j
  disjoint d m
  disjoint d n
  disjoint d o
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint J d
  disjoint f j
  disjoint f m
  disjoint f n
  disjoint f o
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint J f
  disjoint g j
  disjoint g m
  disjoint g n
  disjoint g o
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint J g
  disjoint j m
  disjoint j n
  disjoint j o
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint J j
  disjoint m o
  disjoint J m
  disjoint n o
  disjoint J n
  disjoint o u
  disjoint o v
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint J o
  disjoint J w
  disjoint J z
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V x
  disjoint X o
  disjoint X w
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  assert |- ( J e. ( TopOn ` X ) -> ( J e. Haus <-> A. x e. X A. y e. X ( x =/= y -> E. u e. ( ( nei ` J ) ` { x } ) E. v e. ( ( nei ` J ) ` { y } ) ( u i^i v ) = (/) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cJ
    cha
    wcel
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @1
    vm
    cv
    #
    wcel
    #
    @2
    vn
    cv
    #
    wcel
    #
    @4
    @6
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    cJ
    wrex
    #
    vm
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
    @3
    vu
    cv
    #
    vv
    cv
    #
    cin
    #
    c0
    wceq
    #
    vv
    @2
    csn
    #
    cJ
    cnei
    cfv
    #
    cfv
    #
    wrex
    vu
    @1
    csn
    #
    @20
    cfv
    #
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
    vx
    vy
    vn
    vm
    cJ
    cX
    ishaus2
    @0
    cJ
    ctop
    wcel
    #
    @14
    @26
    wb
    cX
    cJ
    topontop
    @27
    @13
    @25
    vx
    vy
    cX
    cX
    @27
    @12
    @24
    @3
    @27
    @12
    @24
    @27
    @10
    @24
    vm
    vn
    cJ
    cJ
    @27
    @4
    cJ
    wcel
    #
    @6
    cJ
    wcel
    #
    @10
    @24
    wi
    @27
    @28
    @29
    w3a
    #
    @10
    @24
    @30
    @10
    wa
    #
    @4
    @23
    wcel
    #
    @6
    @21
    wcel
    #
    @9
    @24
    @31
    @27
    @28
    @5
    @32
    @30
    @27
    @10
    @27
    @28
    @29
    simp1
    adantr
    #
    @30
    @28
    @10
    @27
    @28
    @29
    simp2
    adantr
    @10
    @5
    @30
    @5
    @7
    @9
    simp1
    adantl
    @1
    cJ
    @4
    opnneip
    syl3anc
    @31
    @27
    @29
    @7
    @33
    @34
    @30
    @29
    @10
    @27
    @28
    @29
    simp3
    adantr
    @10
    @7
    @30
    @5
    @7
    @9
    simp2
    adantl
    @2
    cJ
    @6
    opnneip
    syl3anc
    @10
    @9
    @30
    @5
    @7
    @9
    simp3
    adantl
    @18
    @9
    @4
    @16
    cin
    #
    c0
    wceq
    vu
    vv
    @4
    @6
    @23
    @21
    @15
    @4
    wceq
    @17
    @35
    c0
    @15
    @4
    @16
    ineq1
    eqeq1d
    @16
    @6
    wceq
    @35
    @8
    c0
    @16
    @6
    @4
    ineq2
    eqeq1d
    rspc2ev
    syl3anc
    ex
    3expib
    rexlimdvv
    @27
    @18
    @12
    vu
    vv
    @23
    @21
    @27
    @15
    @23
    wcel
    #
    @22
    @4
    wss
    #
    @4
    @15
    wss
    #
    wa
    #
    vm
    cJ
    wrex
    #
    @16
    @21
    wcel
    #
    @19
    @6
    wss
    #
    @6
    @16
    wss
    #
    wa
    #
    vn
    cJ
    wrex
    #
    @18
    @12
    wi
    #
    @27
    @36
    @40
    @22
    vm
    cJ
    @15
    neii2
    ex
    @27
    @41
    @45
    @19
    vn
    cJ
    @16
    neii2
    ex
    @27
    @40
    @45
    @46
    @27
    @18
    @45
    @40
    @12
    @27
    @18
    @45
    @40
    @12
    wi
    @27
    @18
    @45
    w3a
    #
    @39
    @11
    vm
    cJ
    @39
    @5
    @38
    wa
    #
    @47
    @11
    @5
    @37
    @38
    @1
    @4
    vx
    vex
    snss
    anbi1i
    @27
    @18
    @45
    @48
    @11
    wi
    @27
    @18
    @48
    @45
    @11
    @27
    @18
    @48
    @45
    @11
    wi
    @27
    @18
    @48
    w3a
    @44
    @10
    vn
    cJ
    @18
    @48
    @44
    @10
    wi
    #
    @27
    @18
    @48
    @49
    @48
    @44
    @18
    @10
    @44
    @7
    @43
    wa
    #
    @48
    @18
    @10
    wi
    @7
    @42
    @43
    @2
    @6
    vy
    vex
    snss
    anbi1i
    @48
    @50
    @18
    @10
    @48
    @50
    @18
    w3a
    @5
    @7
    @9
    @5
    @38
    @50
    @18
    simp1l
    @48
    @7
    @43
    @18
    simp2l
    @48
    @50
    @18
    @9
    @38
    @43
    @18
    @9
    wi
    #
    @5
    @7
    @38
    @43
    wa
    @8
    @17
    wss
    #
    @51
    @4
    @15
    @6
    @16
    ss2in
    @52
    @8
    c0
    @17
    c0
    @52
    @8
    c0
    wne
    @17
    c0
    wne
    @8
    @17
    ssn0
    ex
    necon4d
    syl
    ad2ant2l
    3impia
    3jca
    3exp
    syl5bir
    com3r
    imp
    3adant1
    reximdv
    3exp
    com34
    3imp
    syl5bir
    reximdv
    3exp
    com24
    impd
    syl2and
    rexlimdvv
    impbid
    imbi2d
    2ralbidv
    syl
    bitrd
end

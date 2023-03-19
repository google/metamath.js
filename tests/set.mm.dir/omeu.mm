include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "comu.mm"
include "co.mm"
include "coa.mm"
include "wa.mm"
include "wrex.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "omeulem1.mm"
include "opex.mm"
include "isseti.mm"
include "19.41v.mm"
include "mpbiran.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "bitr3i.mm"
include "bitri.mm"
include "sylib.mm"
include "simp2rl.mm"
include "simp3rl.mm"
include "simp2rr.mm"
include "simp3rr.mm"
include "eqtr4d.mm"
include "wb.mm"
include "simp11.mm"
include "simp13.mm"
include "simp2ll.mm"
include "simp2lr.mm"
include "simp3ll.mm"
include "simp3lr.mm"
include "omopth2.mm"
include "syl222anc.mm"
include "mpbid.mm"
include "opeq12.mm"
include "syl.mm"
include "3expia.mm"
include "exp4b.mm"
include "expd.mm"
include "rexlimdvv.mm"
include "imp.mm"
include "expimpd.mm"
include "alrimivv.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "opeq2.mm"
include "cbvrex2v.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "2rexbidv.mm"
include "syl5bb.mm"
include "eu4.mm"
include "sylanbrc.mm"

theorem omeu
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint A r
  disjoint A s
  disjoint A t
  disjoint r s
  disjoint r t
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B r
  disjoint B s
  disjoint B t
  assert |- ( ( A e. On /\ B e. On /\ A =/= (/) ) -> E! z E. x e. On E. y e. A ( z = <. x , y >. /\ ( ( A .o x ) +o y ) = B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    cA
    @5
    comu
    co
    #
    @6
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    vy
    cA
    wrex
    #
    vx
    con0
    wrex
    #
    vz
    wex
    #
    @14
    vt
    cv
    #
    vr
    cv
    #
    vs
    cv
    #
    cop
    #
    wceq
    #
    cA
    @17
    comu
    co
    #
    @18
    coa
    co
    #
    cB
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    vr
    con0
    wrex
    #
    wa
    @4
    @16
    wceq
    #
    wi
    #
    vt
    wal
    vz
    wal
    @14
    vz
    weu
    @3
    @11
    vy
    cA
    wrex
    #
    vx
    con0
    wrex
    #
    @15
    vx
    vy
    cA
    cB
    omeulem1
    @29
    @13
    vz
    wex
    #
    vx
    con0
    wrex
    @15
    @28
    @30
    vx
    con0
    @28
    @12
    vz
    wex
    #
    vy
    cA
    wrex
    @30
    @31
    @11
    vy
    cA
    @31
    @8
    vz
    wex
    @11
    vz
    @7
    @5
    @6
    opex
    isseti
    @8
    @11
    vz
    19.41v
    mpbiran
    rexbii
    @12
    vy
    vz
    cA
    rexcom4
    bitr3i
    rexbii
    @13
    vx
    vz
    con0
    rexcom4
    bitri
    sylib
    @3
    @27
    vz
    vt
    @3
    @14
    @25
    @26
    @3
    @14
    wa
    @24
    @26
    vr
    vs
    con0
    cA
    @3
    @14
    @17
    con0
    wcel
    #
    @18
    cA
    wcel
    #
    wa
    #
    @24
    @26
    wi
    wi
    #
    @3
    @12
    @35
    vx
    vy
    con0
    cA
    @3
    @5
    con0
    wcel
    #
    @6
    cA
    wcel
    #
    wa
    #
    @12
    @35
    @3
    @38
    @12
    wa
    #
    @34
    @24
    @26
    @3
    @39
    @34
    @24
    wa
    #
    @26
    @3
    @39
    @40
    w3a
    #
    @4
    @7
    @16
    @8
    @11
    @38
    @3
    @40
    simp2rl
    @41
    @16
    @19
    @7
    @20
    @23
    @34
    @3
    @39
    simp3rl
    @41
    @5
    @17
    wceq
    #
    @6
    @18
    wceq
    #
    wa
    #
    @7
    @19
    wceq
    @41
    @10
    @22
    wceq
    #
    @44
    @41
    @10
    cB
    @22
    @8
    @11
    @38
    @3
    @40
    simp2rr
    @20
    @23
    @34
    @3
    @39
    simp3rr
    eqtr4d
    @41
    @0
    @2
    @36
    @37
    @32
    @33
    @45
    @44
    wb
    @0
    @1
    @2
    @39
    @40
    simp11
    @0
    @1
    @2
    @39
    @40
    simp13
    @36
    @37
    @12
    @3
    @40
    simp2ll
    @36
    @37
    @12
    @3
    @40
    simp2lr
    @32
    @33
    @24
    @3
    @39
    simp3ll
    @32
    @33
    @24
    @3
    @39
    simp3lr
    cA
    @5
    @6
    @17
    @18
    omopth2
    syl222anc
    mpbid
    @5
    @6
    @17
    @18
    opeq12
    syl
    eqtr4d
    eqtr4d
    3expia
    exp4b
    expd
    rexlimdvv
    imp
    rexlimdvv
    expimpd
    alrimivv
    @14
    @25
    vz
    vt
    @14
    @4
    @19
    wceq
    #
    @23
    wa
    #
    vs
    cA
    wrex
    vr
    con0
    wrex
    @26
    @25
    @12
    @47
    @4
    @17
    @6
    cop
    #
    wceq
    #
    @21
    @6
    coa
    co
    #
    cB
    wceq
    #
    wa
    vx
    vy
    vr
    vs
    con0
    cA
    @42
    @8
    @49
    @11
    @51
    @42
    @7
    @48
    @4
    @5
    @17
    @6
    opeq1
    eqeq2d
    @42
    @10
    @50
    cB
    @42
    @9
    @21
    @6
    coa
    @5
    @17
    cA
    comu
    oveq2
    oveq1d
    eqeq1d
    anbi12d
    @43
    @49
    @46
    @51
    @23
    @43
    @48
    @19
    @4
    @6
    @18
    @17
    opeq2
    eqeq2d
    @43
    @50
    @22
    cB
    @6
    @18
    @21
    coa
    oveq2
    eqeq1d
    anbi12d
    cbvrex2v
    @26
    @47
    @24
    vr
    vs
    con0
    cA
    @26
    @46
    @20
    @23
    @4
    @16
    @19
    eqeq1
    anbi1d
    2rexbidv
    syl5bb
    eu4
    sylanbrc
end

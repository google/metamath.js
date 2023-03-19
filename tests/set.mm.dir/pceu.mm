include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "wex.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "simprl.mm"
include "elq.mm"
include "sylib.mm"
include "ovex.mm"
include "biidd.mm"
include "ceqsexv.mm"
include "exancom.mm"
include "bitr3i.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "bitri.mm"
include "w3a.mm"
include "eqid.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp2.mm"
include "simp3l.mm"
include "pceulem.mm"
include "simp13r.mm"
include "simp3r.mm"
include "3eqtr4d.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "adantrl.mm"
include "impd.mm"
include "alrimivv.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "eu4.mm"
include "sylanbrc.mm"

theorem pceu
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cN: class N
  let vp: setvar p
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let wph: wff ph
  assume pcval.1: |- S = sup ( { n e. NN0 | ( P ^ n ) || x } , RR , < )
  assume pcval.2: |- T = sup ( { n e. NN0 | ( P ^ n ) || y } , RR , < )

  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  disjoint x y
  disjoint x z
  disjoint N x
  disjoint y z
  disjoint N y
  disjoint N z
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint S z
  disjoint T z
  disjoint n p
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n w
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint N p
  disjoint r s
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint N r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint N s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint N t
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint N w
  disjoint P p
  disjoint P s
  disjoint P t
  disjoint P r
  disjoint P w
  disjoint S p
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint T p
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint ph z
  assert |- ( ( P e. Prime /\ ( N e. QQ /\ N =/= 0 ) ) -> E! z E. x e. ZZ E. y e. NN ( N = ( x / y ) /\ z = ( S - T ) ) )

  proof
    cP
    cprime
    wcel
    #
    cN
    cq
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    wa
    #
    cN
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vz
    cv
    #
    cS
    cT
    cmin
    co
    #
    wceq
    #
    wa
    #
    vy
    cn
    wrex
    #
    vx
    cz
    wrex
    #
    vz
    wex
    #
    @13
    cN
    vs
    cv
    #
    vt
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vw
    cv
    #
    cP
    vn
    cv
    cexp
    co
    #
    @15
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @20
    @16
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cmin
    co
    #
    wceq
    #
    wa
    #
    vt
    cn
    wrex
    #
    vs
    cz
    wrex
    #
    wa
    @8
    @19
    wceq
    #
    wi
    #
    vw
    wal
    vz
    wal
    @13
    vz
    weu
    @3
    @7
    vy
    cn
    wrex
    #
    vx
    cz
    wrex
    #
    @14
    @3
    @1
    @35
    @0
    @1
    @2
    simprl
    vx
    vy
    cN
    elq
    sylib
    @35
    @12
    vz
    wex
    #
    vx
    cz
    wrex
    @14
    @34
    @36
    vx
    cz
    @34
    @11
    vz
    wex
    #
    vy
    cn
    wrex
    @36
    @7
    @37
    vy
    cn
    @7
    @10
    @7
    wa
    vz
    wex
    @37
    @7
    @7
    vz
    @9
    cS
    cT
    cmin
    ovex
    @10
    @7
    biidd
    ceqsexv
    @10
    @7
    vz
    exancom
    bitr3i
    rexbii
    @11
    vy
    vz
    cn
    rexcom4
    bitri
    rexbii
    @12
    vx
    vz
    cz
    rexcom4
    bitri
    sylib
    @3
    @33
    vz
    vw
    @3
    @13
    @31
    @32
    @3
    @11
    @31
    @32
    wi
    #
    vx
    vy
    cz
    cn
    @0
    @2
    @4
    cz
    wcel
    @5
    cn
    wcel
    wa
    #
    @11
    @38
    wi
    wi
    @1
    @0
    @2
    wa
    #
    @39
    @11
    @38
    @40
    @39
    @11
    w3a
    #
    @29
    @32
    vs
    vt
    cz
    cn
    @41
    @15
    cz
    wcel
    @16
    cn
    wcel
    wa
    #
    @29
    @32
    @41
    @42
    @29
    w3a
    #
    @9
    @27
    @8
    @19
    @43
    vx
    vy
    vt
    cP
    cS
    cT
    @23
    vn
    cN
    @26
    vs
    pcval.1
    pcval.2
    @23
    eqid
    @26
    eqid
    @0
    @2
    @39
    @11
    @42
    @29
    simp11l
    @0
    @2
    @39
    @11
    @42
    @29
    simp11r
    @40
    @39
    @11
    @42
    @29
    simp12
    @7
    @10
    @40
    @39
    @42
    @29
    simp13l
    @41
    @42
    @29
    simp2
    @41
    @42
    @18
    @28
    simp3l
    pceulem
    @7
    @10
    @40
    @39
    @42
    @29
    simp13r
    @41
    @42
    @18
    @28
    simp3r
    3eqtr4d
    3exp
    rexlimdvv
    3exp
    adantrl
    rexlimdvv
    impd
    alrimivv
    @13
    @31
    vz
    vw
    @32
    @13
    @7
    @19
    @9
    wceq
    #
    wa
    #
    vy
    cn
    wrex
    #
    vx
    cz
    wrex
    @31
    @32
    @11
    @45
    vx
    vy
    cz
    cn
    @32
    @10
    @44
    @7
    @8
    @19
    @9
    eqeq1
    anbi2d
    2rexbidv
    @46
    @30
    vx
    vs
    cz
    @4
    @15
    wceq
    #
    @46
    cN
    @15
    @5
    cdiv
    co
    #
    wceq
    #
    @19
    @23
    cT
    cmin
    co
    #
    wceq
    #
    wa
    #
    vy
    cn
    wrex
    @30
    @47
    @45
    @52
    vy
    cn
    @47
    @7
    @49
    @44
    @51
    @47
    @6
    @48
    cN
    @4
    @15
    @5
    cdiv
    oveq1
    eqeq2d
    @47
    @9
    @50
    @19
    @47
    cS
    @23
    cT
    cmin
    @47
    cS
    @20
    @4
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    @23
    pcval.1
    @47
    cr
    @54
    @22
    clt
    @47
    @53
    @21
    vn
    cn0
    @4
    @15
    @20
    cdvds
    breq2
    rabbidv
    supeq1d
    syl5eq
    oveq1d
    eqeq2d
    anbi12d
    rexbidv
    @52
    @29
    vy
    vt
    cn
    @5
    @16
    wceq
    #
    @49
    @18
    @51
    @28
    @55
    @48
    @17
    cN
    @5
    @16
    @15
    cdiv
    oveq2
    eqeq2d
    @55
    @50
    @27
    @19
    @55
    cT
    @26
    @23
    cmin
    @55
    cT
    @20
    @5
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    @26
    pcval.2
    @55
    cr
    @57
    @25
    clt
    @55
    @56
    @24
    vn
    cn0
    @5
    @16
    @20
    cdvds
    breq2
    rabbidv
    supeq1d
    syl5eq
    oveq2d
    eqeq2d
    anbi12d
    cbvrexv
    syl6bb
    cbvrexv
    syl6bb
    eu4
    sylanbrc
end

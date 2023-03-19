include "cprime.mm"
include "wcel.mm"
include "cq.mm"
include "cc0.mm"
include "wne.mm"
include "cpc.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "wceq.mm"
include "cmin.mm"
include "wa.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "cio.mm"
include "cpnf.mm"
include "cif.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "breq1d.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "bi2anan9r.mm"
include "2rexbidv.mm"
include "iotabidv.mm"
include "ifbieq2d.mm"
include "df-pc.mm"
include "pnfex.mm"
include "iotaex.mm"
include "ifex.mm"
include "ovmpt2a.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"
include "anasss.mm"

theorem pcval
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
  assert |- ( ( P e. Prime /\ ( N e. QQ /\ N =/= 0 ) ) -> ( P pCnt N ) = ( iota z E. x e. ZZ E. y e. NN ( N = ( x / y ) /\ z = ( S - T ) ) ) )

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
    cP
    cN
    cpc
    co
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
    vx
    cz
    wrex
    #
    vz
    cio
    #
    wceq
    @0
    @1
    wa
    @2
    @3
    cN
    cc0
    wceq
    #
    cpnf
    @13
    cif
    #
    @13
    vp
    vr
    cP
    cN
    cprime
    cq
    vr
    cv
    #
    cc0
    wceq
    #
    cpnf
    @16
    @6
    wceq
    #
    @8
    vp
    cv
    #
    vn
    cv
    #
    cexp
    co
    #
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
    #
    @21
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
    #
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
    vx
    cz
    wrex
    #
    vz
    cio
    #
    cif
    @15
    cpc
    @19
    cP
    wceq
    #
    @16
    cN
    wceq
    #
    wa
    #
    @17
    @14
    @32
    @13
    cpnf
    @35
    @16
    cN
    cc0
    @33
    @34
    simpr
    eqeq1d
    @35
    @31
    @12
    vz
    @35
    @30
    @11
    vx
    vy
    cz
    cn
    @34
    @18
    @7
    @33
    @29
    @10
    @16
    cN
    @6
    eqeq1
    @33
    @28
    @9
    @8
    @33
    @24
    cS
    @27
    cT
    cmin
    @33
    @24
    cP
    @20
    cexp
    co
    #
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
    cS
    @33
    cr
    @23
    @38
    clt
    @33
    @22
    @37
    vn
    cn0
    @33
    @21
    @36
    @4
    cdvds
    @19
    cP
    @20
    cexp
    oveq1
    #
    breq1d
    rabbidv
    supeq1d
    pcval.1
    syl6eqr
    @33
    @27
    @36
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
    cT
    @33
    cr
    @26
    @41
    clt
    @33
    @25
    @40
    vn
    cn0
    @33
    @21
    @36
    @5
    cdvds
    @39
    breq1d
    rabbidv
    supeq1d
    pcval.2
    syl6eqr
    oveq12d
    eqeq2d
    bi2anan9r
    2rexbidv
    iotabidv
    ifbieq2d
    vx
    vy
    vz
    vn
    vr
    vp
    df-pc
    @14
    cpnf
    @13
    pnfex
    @12
    vz
    iotaex
    ifex
    ovmpt2a
    cN
    cc0
    cpnf
    @13
    ifnefalse
    sylan9eq
    anasss
end

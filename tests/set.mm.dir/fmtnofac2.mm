include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cfmtno.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "c1.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "breq1.mm"
include "anbi2d.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "weq.mm"
include "cc0.mm"
include "0nn0.mm"
include "a1i.mm"
include "wb.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "2nn0.mm"
include "eluzge2nn0.mm"
include "nn0addcld.mm"
include "nn0expcld.mm"
include "nn0cnd.mm"
include "mul02d.mm"
include "0p1e1.mm"
include "syl6req.mm"
include "rspcedvd.mm"
include "adantr.mm"
include "cprime.mm"
include "simpl.mm"
include "simprr.mm"
include "wss.mm"
include "w3a.mm"
include "nnssnn0.mm"
include "fmtnoprmfac2.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "syl3anc.mm"
include "ex.mm"
include "fmtnofac2lem.mm"
include "prmind.mm"
include "expd.mm"
include "3imp21.mm"

theorem fmtnofac2
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let vz: setvar z

  disjoint M k
  disjoint N k
  disjoint M x
  disjoint k x
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint k m
  disjoint k n
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k x
  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ M e. NN /\ M || ( FermatNo ` N ) ) -> E. k e. NN0 M = ( ( k x. ( 2 ^ ( N + 2 ) ) ) + 1 ) )

  proof
    cM
    cn
    wcel
    #
    cN
    c2
    cuz
    cfv
    wcel
    #
    cM
    cN
    cfmtno
    cfv
    #
    cdvds
    wbr
    #
    cM
    vk
    cv
    #
    c2
    cN
    c2
    caddc
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cn0
    wrex
    #
    @0
    @1
    @3
    @10
    @1
    vx
    cv
    #
    @2
    cdvds
    wbr
    #
    wa
    #
    @11
    @8
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    @1
    c1
    @2
    cdvds
    wbr
    #
    wa
    #
    c1
    @8
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    @1
    vy
    cv
    #
    @2
    cdvds
    wbr
    #
    wa
    #
    @20
    @8
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    @1
    vz
    cv
    #
    @2
    cdvds
    wbr
    #
    wa
    #
    @25
    @8
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    @1
    @20
    @25
    cmul
    co
    #
    @2
    cdvds
    wbr
    #
    wa
    #
    @30
    @8
    wceq
    #
    vk
    cn0
    wrex
    #
    wi
    @1
    @3
    wa
    #
    @10
    wi
    vx
    vy
    vz
    cM
    @11
    c1
    wceq
    #
    @13
    @17
    @15
    @19
    @36
    @12
    @16
    @1
    @11
    c1
    @2
    cdvds
    breq1
    anbi2d
    @36
    @14
    @18
    vk
    cn0
    @11
    c1
    @8
    eqeq1
    rexbidv
    imbi12d
    vx
    vy
    weq
    #
    @13
    @22
    @15
    @24
    @37
    @12
    @21
    @1
    @11
    @20
    @2
    cdvds
    breq1
    anbi2d
    @37
    @14
    @23
    vk
    cn0
    @11
    @20
    @8
    eqeq1
    rexbidv
    imbi12d
    vx
    vz
    weq
    #
    @13
    @27
    @15
    @29
    @38
    @12
    @26
    @1
    @11
    @25
    @2
    cdvds
    breq1
    anbi2d
    @38
    @14
    @28
    vk
    cn0
    @11
    @25
    @8
    eqeq1
    rexbidv
    imbi12d
    @11
    @30
    wceq
    #
    @13
    @32
    @15
    @34
    @39
    @12
    @31
    @1
    @11
    @30
    @2
    cdvds
    breq1
    anbi2d
    @39
    @14
    @33
    vk
    cn0
    @11
    @30
    @8
    eqeq1
    rexbidv
    imbi12d
    @11
    cM
    wceq
    #
    @13
    @35
    @15
    @10
    @40
    @12
    @3
    @1
    @11
    cM
    @2
    cdvds
    breq1
    anbi2d
    @40
    @14
    @9
    vk
    cn0
    @11
    cM
    @8
    eqeq1
    rexbidv
    imbi12d
    @1
    @19
    @16
    @1
    @18
    c1
    cc0
    @6
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cc0
    cn0
    cc0
    cn0
    wcel
    @1
    0nn0
    a1i
    @4
    cc0
    wceq
    #
    @18
    @43
    wb
    @1
    @44
    @8
    @42
    c1
    @44
    @7
    @41
    c1
    caddc
    @4
    cc0
    @6
    cmul
    oveq1
    oveq1d
    eqeq2d
    adantl
    @1
    @42
    cc0
    c1
    caddc
    co
    c1
    @1
    @41
    cc0
    c1
    caddc
    @1
    @6
    @1
    @6
    @1
    c2
    @5
    c2
    cn0
    wcel
    @1
    2nn0
    a1i
    #
    @1
    cN
    c2
    cN
    eluzge2nn0
    @45
    nn0addcld
    nn0expcld
    nn0cnd
    mul02d
    oveq1d
    0p1e1
    syl6req
    rspcedvd
    adantr
    @11
    cprime
    wcel
    #
    @13
    @15
    @46
    @13
    wa
    @1
    @46
    @12
    @15
    @13
    @1
    @46
    @1
    @12
    simpl
    adantl
    @46
    @13
    simpl
    @46
    @1
    @12
    simprr
    cn
    cn0
    wss
    @1
    @46
    @12
    w3a
    @14
    vk
    cn
    wrex
    @15
    nnssnn0
    @11
    vk
    cN
    fmtnoprmfac2
    @14
    vk
    cn
    cn0
    ssrexv
    mpsyl
    syl3anc
    ex
    vy
    vz
    vk
    cN
    fmtnofac2lem
    prmind
    expd
    3imp21
end

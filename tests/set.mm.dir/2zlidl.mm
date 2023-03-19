include "wcel.mm"
include "cz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wral.mm"
include "c2.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cc0.mm"
include "0even.mm"
include "ne0ii.mm"
include "wa.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "anbi12i.mm"
include "simpl.mm"
include "simprll.mm"
include "zmulcld.mm"
include "adantl.mm"
include "zaddcld.mm"
include "wi.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "simpr.mm"
include "adantr.mm"
include "simp-4l.mm"
include "ad2antrl.mm"
include "oveq2d.mm"
include "simpllr.mm"
include "oveq12d.mm"
include "eqeqan12d.mm"
include "cc.mm"
include "zcn.mm"
include "2cnd.mm"
include "mul12d.mm"
include "oveq1d.mm"
include "mulcld.mm"
include "ad4antr.mm"
include "adddid.mm"
include "eqtr4d.mm"
include "rspcedvd.mm"
include "exp41.mm"
include "rexlimiva.mm"
include "sylbi.mm"
include "impcom.mm"
include "expdcom.mm"
include "imp.mm"
include "sylanbrc.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "rgen.mm"
include "zring.mm"
include "zringbas.mm"
include "zringplusg.mm"
include "zringmulr.mm"
include "islidl.mm"
include "mpbir3an.mm"

theorem 2zlidl
  let vx: setvar x
  let vz: setvar z
  let cU: class U
  let cE: class E
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zlidl.u: |- U = ( LIdeal ` ZZring )

  disjoint x z
  disjoint x z
  disjoint a b
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a x
  disjoint a z
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b x
  disjoint b z
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint i z
  disjoint j k
  disjoint j x
  disjoint j z
  disjoint k x
  disjoint k z
  disjoint E i
  disjoint E j
  disjoint E k
  disjoint k x
  assert |- E e. U

  proof
    cE
    cU
    wcel
    cE
    cz
    wss
    cE
    c0
    wne
    vi
    cv
    #
    vj
    cv
    #
    cmul
    co
    #
    vk
    cv
    #
    caddc
    co
    #
    cE
    wcel
    #
    vk
    cE
    wral
    vj
    cE
    wral
    #
    vi
    cz
    wral
    cE
    vz
    cv
    #
    c2
    vx
    cv
    #
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    vz
    cz
    crab
    cz
    2zrng.e
    @11
    vz
    cz
    ssrab2
    eqsstri
    cc0
    cE
    vx
    vz
    cE
    2zrng.e
    0even
    ne0ii
    @6
    vi
    cz
    @0
    cz
    wcel
    #
    @5
    vj
    vk
    cE
    cE
    @1
    cE
    wcel
    #
    @3
    cE
    wcel
    #
    wa
    @12
    @1
    cz
    wcel
    #
    @1
    @9
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    #
    @3
    cz
    wcel
    #
    @3
    @9
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    #
    wa
    #
    @5
    @13
    @18
    @14
    @22
    @11
    @17
    vz
    @1
    cz
    cE
    vz
    vj
    weq
    @10
    @16
    vx
    cz
    @7
    @1
    @9
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @11
    @21
    vz
    @3
    cz
    cE
    vz
    vk
    weq
    @10
    @20
    vx
    cz
    @7
    @3
    @9
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    anbi12i
    @12
    @23
    wa
    #
    @4
    cz
    wcel
    @4
    @9
    wceq
    #
    vx
    cz
    wrex
    #
    @5
    @24
    @2
    @3
    @24
    @0
    @1
    @12
    @23
    simpl
    @12
    @15
    @17
    @22
    simprll
    zmulcld
    @23
    @19
    @12
    @22
    @19
    @18
    @19
    @21
    simpl
    adantl
    adantl
    zaddcld
    @23
    @12
    @26
    @18
    @22
    @12
    @26
    wi
    #
    @17
    @15
    @22
    @27
    wi
    #
    @17
    @1
    c2
    va
    cv
    #
    cmul
    co
    #
    wceq
    #
    va
    cz
    wrex
    @15
    @28
    wi
    #
    @16
    @31
    vx
    va
    cz
    vx
    va
    weq
    @9
    @30
    @1
    @8
    @29
    c2
    cmul
    oveq2
    eqeq2d
    cbvrexv
    @31
    @32
    va
    cz
    @22
    @29
    cz
    wcel
    #
    @31
    wa
    #
    @15
    @27
    @21
    @19
    @34
    @15
    wa
    #
    @27
    wi
    #
    @21
    @3
    c2
    vb
    cv
    #
    cmul
    co
    #
    wceq
    #
    vb
    cz
    wrex
    @19
    @36
    wi
    #
    @20
    @39
    vx
    vb
    cz
    vx
    vb
    weq
    @9
    @38
    @3
    @8
    @37
    c2
    cmul
    oveq2
    eqeq2d
    cbvrexv
    @39
    @40
    vb
    cz
    @37
    cz
    wcel
    #
    @39
    wa
    #
    @19
    @35
    @12
    @26
    @42
    @19
    wa
    #
    @35
    wa
    #
    @12
    wa
    #
    @25
    @0
    @30
    cmul
    co
    #
    @38
    caddc
    co
    #
    c2
    @0
    @29
    cmul
    co
    #
    @37
    caddc
    co
    #
    cmul
    co
    #
    wceq
    vx
    @49
    cz
    @45
    @48
    @37
    @45
    @0
    @29
    @44
    @12
    simpr
    @44
    @33
    @12
    @43
    @33
    @31
    @15
    simprll
    adantr
    zmulcld
    @41
    @39
    @19
    @35
    @12
    simp-4l
    zaddcld
    @45
    @8
    @49
    wceq
    @4
    @47
    @9
    @50
    @44
    @4
    @47
    wceq
    @12
    @44
    @2
    @46
    @3
    @38
    caddc
    @44
    @1
    @30
    @0
    cmul
    @34
    @31
    @43
    @15
    @33
    @31
    simpr
    ad2antrl
    oveq2d
    @41
    @39
    @19
    @35
    simpllr
    oveq12d
    adantr
    @8
    @49
    c2
    cmul
    oveq2
    eqeqan12d
    @45
    @47
    c2
    @48
    cmul
    co
    #
    @38
    caddc
    co
    @50
    @45
    @46
    @51
    @38
    caddc
    @45
    @0
    c2
    @29
    @12
    @0
    cc
    wcel
    @44
    @0
    zcn
    adantl
    #
    @45
    2cnd
    #
    @44
    @29
    cc
    wcel
    #
    @12
    @34
    @54
    @43
    @15
    @33
    @54
    @31
    @29
    zcn
    adantr
    ad2antrl
    adantr
    #
    mul12d
    oveq1d
    @45
    c2
    @48
    @37
    @53
    @45
    @0
    @29
    @52
    @55
    mulcld
    @41
    @37
    cc
    wcel
    @39
    @19
    @35
    @12
    @37
    zcn
    ad4antr
    adddid
    eqtr4d
    rspcedvd
    exp41
    rexlimiva
    sylbi
    impcom
    expdcom
    rexlimiva
    sylbi
    impcom
    imp
    impcom
    @11
    @26
    vz
    @4
    cz
    cE
    @7
    @4
    wceq
    @10
    @25
    vx
    cz
    @7
    @4
    @9
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    sylanbrc
    sylan2b
    ralrimivva
    rgen
    vi
    cz
    caddc
    zring
    cmul
    cU
    cE
    vj
    vk
    2zlidl.u
    zringbas
    zringplusg
    zringmulr
    islidl
    mpbir3an
end

include "cwdom.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wrex.mm"
include "wral.mm"
include "cun.mm"
include "wex.mm"
include "brwdom3i.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "cvv.mm"
include "wcel.mm"
include "cif.mm"
include "relwdom.mm"
include "brrelexi.mm"
include "unexg.mm"
include "syl2an.mm"
include "3adant3.mm"
include "brrelex2i.mm"
include "wi.mm"
include "wo.mm"
include "elun.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "wss.mm"
include "ssun1.mm"
include "iftrue.mm"
include "fveq1d.mm"
include "biimprd.mm"
include "reximia.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "sylbi.mm"
include "syl.mm"
include "ancoms.mm"
include "adantlr.mm"
include "adantll.mm"
include "syl6bb.mm"
include "rspccva.mm"
include "ssun2.mm"
include "wn.mm"
include "minel.mm"
include "iffalsed.mm"
include "reximdva.mm"
include "imp.mm"
include "sylan2.mm"
include "anassrs.mm"
include "adantlrl.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "expl.mm"
include "3ad2ant3.mm"
include "impl.mm"
include "wdom2d.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem unwdomg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A ~<_* B /\ C ~<_* D /\ ( B i^i D ) = (/) ) -> ( A u. C ) ~<_* ( B u. D ) )

  proof
    cA
    cB
    cwdom
    wbr
    #
    cC
    cD
    cwdom
    wbr
    #
    cB
    cD
    cin
    c0
    wceq
    #
    w3a
    #
    va
    cv
    #
    vb
    cv
    #
    vf
    cv
    #
    cfv
    #
    wceq
    #
    vb
    cB
    wrex
    #
    va
    cA
    wral
    #
    cA
    cC
    cun
    #
    cB
    cD
    cun
    #
    cwdom
    wbr
    #
    vf
    @0
    @1
    @10
    vf
    wex
    @2
    va
    vb
    vf
    cA
    cB
    brwdom3i
    3ad2ant1
    @3
    @10
    wa
    #
    @4
    @5
    vg
    cv
    #
    cfv
    #
    wceq
    #
    vb
    cD
    wrex
    #
    va
    cC
    wral
    #
    vg
    wex
    #
    @13
    @3
    @20
    @10
    @1
    @0
    @20
    @2
    va
    vb
    vg
    cC
    cD
    brwdom3i
    3ad2ant2
    adantr
    @14
    @19
    @13
    vg
    @3
    @10
    @19
    @13
    @3
    @10
    @19
    wa
    #
    wa
    vy
    vz
    @11
    @12
    cvv
    cvv
    vz
    cv
    #
    @22
    cB
    wcel
    #
    @6
    @15
    cif
    #
    cfv
    #
    @3
    @11
    cvv
    wcel
    #
    @21
    @0
    @1
    @26
    @2
    @0
    cA
    cvv
    wcel
    cC
    cvv
    wcel
    @26
    @1
    cA
    cB
    cwdom
    relwdom
    brrelexi
    cC
    cD
    cwdom
    relwdom
    brrelexi
    cA
    cC
    cvv
    cvv
    unexg
    syl2an
    3adant3
    adantr
    @3
    @12
    cvv
    wcel
    #
    @21
    @0
    @1
    @27
    @2
    @0
    cB
    cvv
    wcel
    cD
    cvv
    wcel
    @27
    @1
    cA
    cB
    cwdom
    relwdom
    brrelex2i
    cC
    cD
    cwdom
    relwdom
    brrelex2i
    cB
    cD
    cvv
    cvv
    unexg
    syl2an
    3adant3
    adantr
    @3
    @21
    vy
    cv
    #
    @11
    wcel
    #
    @28
    @25
    wceq
    #
    vz
    @12
    wrex
    #
    @2
    @0
    @21
    @29
    wa
    @31
    wi
    @1
    @2
    @21
    @29
    @31
    @29
    @2
    @21
    wa
    #
    @28
    cA
    wcel
    #
    @28
    cC
    wcel
    #
    wo
    @31
    @28
    cA
    cC
    elun
    @32
    @33
    @31
    @34
    @21
    @33
    @31
    @2
    @10
    @33
    @31
    @19
    @33
    @10
    @31
    @33
    @10
    wa
    @28
    @7
    wceq
    #
    vb
    cB
    wrex
    #
    @31
    @9
    @36
    va
    @28
    cA
    @4
    @28
    wceq
    #
    @8
    @35
    vb
    cB
    @4
    @28
    @7
    eqeq1
    rexbidv
    rspcva
    @36
    @28
    @22
    @6
    cfv
    #
    wceq
    #
    vz
    cB
    wrex
    #
    @31
    @35
    @39
    vb
    vz
    cB
    @5
    @22
    wceq
    #
    @7
    @38
    @28
    @5
    @22
    @6
    fveq2
    eqeq2d
    cbvrexv
    cB
    @12
    wss
    @40
    @30
    vz
    cB
    wrex
    @31
    cB
    cD
    ssun1
    @39
    @30
    vz
    cB
    @23
    @30
    @39
    @23
    @25
    @38
    @28
    @23
    @22
    @24
    @6
    @23
    @6
    @15
    iftrue
    fveq1d
    eqeq2d
    biimprd
    reximia
    @30
    vz
    cB
    @12
    ssrexv
    mpsyl
    sylbi
    syl
    ancoms
    adantlr
    adantll
    @2
    @19
    @34
    @31
    @10
    @2
    @19
    @34
    @31
    @19
    @34
    wa
    @2
    @28
    @22
    @15
    cfv
    #
    wceq
    #
    vz
    cD
    wrex
    #
    @31
    @18
    @44
    va
    @28
    cC
    @37
    @18
    @28
    @16
    wceq
    #
    vb
    cD
    wrex
    @44
    @37
    @17
    @45
    vb
    cD
    @4
    @28
    @16
    eqeq1
    rexbidv
    @45
    @43
    vb
    vz
    cD
    @41
    @16
    @42
    @28
    @5
    @22
    @15
    fveq2
    eqeq2d
    cbvrexv
    syl6bb
    rspccva
    cD
    @12
    wss
    @2
    @44
    wa
    @30
    vz
    cD
    wrex
    #
    @31
    cD
    cB
    ssun2
    @2
    @44
    @46
    @2
    @43
    @30
    vz
    cD
    @2
    @22
    cD
    wcel
    #
    wa
    #
    @30
    @43
    @48
    @25
    @42
    @28
    @48
    @22
    @24
    @15
    @48
    @23
    @6
    @15
    @47
    @2
    @23
    wn
    @22
    cD
    cB
    minel
    ancoms
    iffalsed
    fveq1d
    eqeq2d
    biimprd
    reximdva
    imp
    @30
    vz
    cD
    @12
    ssrexv
    mpsyl
    sylan2
    anassrs
    adantlrl
    jaodan
    sylan2b
    expl
    3ad2ant3
    impl
    wdom2d
    expr
    exlimdv
    mpd
    exlimddv
end

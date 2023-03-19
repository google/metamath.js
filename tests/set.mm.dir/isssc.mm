include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "cxp.mm"
include "cfv.mm"
include "cpw.mm"
include "cixp.mm"
include "wcel.mm"
include "wrex.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wss.mm"
include "co.mm"
include "wfn.mm"
include "brssc.mm"
include "cdm.mm"
include "fndm.mm"
include "adantl.mm"
include "adantr.mm"
include "syl.mm"
include "eqtr3d.mm"
include "dmeqd.mm"
include "dmxpid.mm"
include "3eqtr3g.mm"
include "ex.mm"
include "id.mm"
include "sqxpeqd.mm"
include "fneq2d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "wb.mm"
include "pweq.mm"
include "rexeqdv.mm"
include "ceqsexgv.mm"
include "bitrd.mm"
include "df-rex.mm"
include "cvv.mm"
include "w3a.mm"
include "3anass.mm"
include "elixp2.mm"
include "vex.mm"
include "xpex.mm"
include "fnex.mm"
include "mpan2.mm"
include "pm4.71ri.mm"
include "3bitr4i.mm"
include "anbi2d.mm"
include "an12.mm"
include "syl6bb.mm"
include "wi.mm"
include "exsimpl.mm"
include "isset.mm"
include "sylibr.mm"
include "a1i.mm"
include "ssexg.mm"
include "expcom.mm"
include "adantrd.mm"
include "elpw.mm"
include "sseq1.mm"
include "raleqdv.mm"
include "cop.mm"
include "fvex.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "sseq12d.mm"
include "ralxp.mm"
include "anbi12d.mm"
include "pm5.21ndd.mm"
include "3bitrd.mm"

theorem isssc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cH: class H
  let cJ: class J
  let cV: class V
  let vs: setvar s
  let vt: setvar t
  let vz: setvar z
  assume isssc.1: |- ( ph -> H Fn ( S X. S ) )
  assume isssc.2: |- ( ph -> J Fn ( T X. T ) )
  assume isssc.3: |- ( ph -> T e. V )

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint S x
  disjoint S y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint H s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint H t
  disjoint x z
  disjoint y z
  disjoint H z
  disjoint J s
  disjoint J t
  disjoint J z
  disjoint ph s
  disjoint ph t
  disjoint S s
  disjoint S z
  disjoint T s
  disjoint T t
  assert |- ( ph -> ( H C_cat J <-> ( S C_ T /\ A. x e. S A. y e. S ( x H y ) C_ ( x J y ) ) ) )

  proof
    wph
    cH
    cJ
    cssc
    wbr
    #
    cH
    vz
    vs
    cv
    #
    @1
    cxp
    #
    vz
    cv
    #
    cJ
    cfv
    #
    cpw
    #
    cixp
    wcel
    #
    vs
    cT
    cpw
    #
    wrex
    #
    @1
    cS
    wceq
    #
    @1
    @7
    wcel
    #
    @3
    cH
    cfv
    #
    @5
    wcel
    #
    vz
    @2
    wral
    #
    wa
    #
    wa
    #
    vs
    wex
    #
    cS
    cT
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @18
    @19
    cJ
    co
    #
    wss
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    wa
    #
    wph
    @0
    vt
    cv
    #
    cT
    wceq
    #
    @6
    vs
    @25
    cpw
    #
    wrex
    #
    wa
    #
    vt
    wex
    #
    @8
    @0
    cJ
    @25
    @25
    cxp
    #
    wfn
    #
    @28
    wa
    #
    vt
    wex
    wph
    @30
    vz
    vt
    cH
    cJ
    vs
    brssc
    wph
    @33
    @29
    vt
    wph
    @32
    @26
    @28
    wph
    @32
    @26
    wph
    @32
    @26
    wph
    @32
    wa
    #
    @31
    cdm
    cT
    cT
    cxp
    #
    cdm
    @25
    cT
    @34
    @31
    @35
    @34
    cJ
    cdm
    #
    @31
    @35
    @32
    @36
    @31
    wceq
    wph
    @31
    cJ
    fndm
    adantl
    @34
    cJ
    @35
    wfn
    #
    @36
    @35
    wceq
    wph
    @37
    @32
    isssc.2
    adantr
    @35
    cJ
    fndm
    syl
    eqtr3d
    dmeqd
    @25
    dmxpid
    cT
    dmxpid
    3eqtr3g
    ex
    wph
    @32
    @26
    @37
    isssc.2
    @26
    @31
    @35
    cJ
    @26
    @25
    cT
    @26
    id
    sqxpeqd
    fneq2d
    syl5ibrcom
    impbid
    anbi1d
    exbidv
    syl5bb
    wph
    cT
    cV
    wcel
    #
    @30
    @8
    wb
    isssc.3
    @28
    @8
    vt
    cT
    cV
    @26
    @6
    vs
    @27
    @7
    @25
    cT
    pweq
    rexeqdv
    ceqsexgv
    syl
    bitrd
    @8
    @10
    @6
    wa
    #
    vs
    wex
    wph
    @16
    @6
    vs
    @7
    df-rex
    wph
    @39
    @15
    vs
    wph
    @39
    @10
    @9
    @13
    wa
    #
    wa
    @15
    wph
    @6
    @40
    @10
    @6
    cH
    @2
    wfn
    #
    @13
    wa
    #
    wph
    @40
    cH
    cvv
    wcel
    #
    @41
    @13
    w3a
    @43
    @42
    wa
    @6
    @42
    @43
    @41
    @13
    3anass
    vz
    @2
    @5
    cH
    elixp2
    @42
    @43
    @41
    @43
    @13
    @41
    @2
    cvv
    wcel
    @43
    @1
    @1
    vs
    vex
    #
    @44
    xpex
    @2
    cvv
    cH
    fnex
    mpan2
    adantr
    pm4.71ri
    3bitr4i
    wph
    @41
    @9
    @13
    wph
    @41
    @9
    wph
    @41
    @9
    wph
    @41
    wa
    #
    @2
    cdm
    cS
    cS
    cxp
    #
    cdm
    @1
    cS
    @45
    @2
    @46
    @45
    cH
    cdm
    #
    @2
    @46
    @41
    @47
    @2
    wceq
    wph
    @2
    cH
    fndm
    adantl
    @45
    cH
    @46
    wfn
    #
    @47
    @46
    wceq
    wph
    @48
    @41
    isssc.1
    adantr
    @46
    cH
    fndm
    syl
    eqtr3d
    dmeqd
    @1
    dmxpid
    cS
    dmxpid
    3eqtr3g
    ex
    wph
    @41
    @9
    @48
    isssc.1
    @9
    @2
    @46
    cH
    @9
    @1
    cS
    @9
    id
    sqxpeqd
    #
    fneq2d
    syl5ibrcom
    impbid
    anbi1d
    syl5bb
    anbi2d
    @10
    @9
    @13
    an12
    syl6bb
    exbidv
    syl5bb
    wph
    cS
    cvv
    wcel
    #
    @16
    @24
    @16
    @50
    wi
    wph
    @16
    @9
    vs
    wex
    @50
    @9
    @14
    vs
    exsimpl
    vs
    cS
    isset
    sylibr
    a1i
    wph
    @17
    @50
    @23
    wph
    @38
    @17
    @50
    wi
    isssc.3
    @17
    @38
    @50
    cS
    cT
    cV
    ssexg
    expcom
    syl
    adantrd
    @50
    @16
    @24
    wb
    wi
    wph
    @14
    @24
    vs
    cS
    cvv
    @9
    @10
    @17
    @13
    @23
    @10
    @1
    cT
    wss
    @9
    @17
    @1
    cT
    @44
    elpw
    @1
    cS
    cT
    sseq1
    syl5bb
    @9
    @13
    @12
    vz
    @46
    wral
    @23
    @9
    @12
    vz
    @2
    @46
    @49
    raleqdv
    @12
    @22
    vz
    vx
    vy
    cS
    cS
    @12
    @11
    @4
    wss
    @3
    @18
    @19
    cop
    #
    wceq
    #
    @22
    @11
    @4
    @3
    cH
    fvex
    elpw
    @52
    @11
    @20
    @4
    @21
    @52
    @11
    @51
    cH
    cfv
    @20
    @3
    @51
    cH
    fveq2
    @18
    @19
    cH
    df-ov
    syl6eqr
    @52
    @4
    @51
    cJ
    cfv
    @21
    @3
    @51
    cJ
    fveq2
    @18
    @19
    cJ
    df-ov
    syl6eqr
    sseq12d
    syl5bb
    ralxp
    syl6bb
    anbi12d
    ceqsexgv
    a1i
    pm5.21ndd
    3bitrd
end

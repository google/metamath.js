include "cr.mm"
include "cxp.mm"
include "cc.mm"
include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ovmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "recnd.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "wa.mm"
include "wb.mm"
include "jca.mm"
include "cru.mm"
include "syl2an.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "vtoclga.mm"
include "eqeqan12d.mm"
include "fvex.mm"
include "opth.mm"
include "syl6bb.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "wrex.mm"
include "cnre.mm"
include "eqeq2d.mm"
include "2rexbiia.mm"
include "sylibr.mm"
include "rexxp.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem cnref1o
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume cnref1o.1: |- F = ( x e. RR , y e. RR |-> ( x + ( _i x. y ) ) )

  disjoint x y
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w z
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint x z
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint y z
  assert |- F : ( RR X. RR ) -1-1-onto-> CC

  proof
    cr
    cr
    cxp
    #
    cc
    cF
    wf1o
    @0
    cc
    cF
    wf1
    #
    @0
    cc
    cF
    wfo
    #
    @1
    @0
    cc
    cF
    wf
    #
    vz
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vw
    @0
    wral
    vz
    @0
    wral
    @3
    cF
    @0
    wfn
    @5
    cc
    wcel
    #
    vz
    @0
    wral
    vx
    vy
    cr
    cr
    vx
    cv
    #
    ci
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    cF
    cnref1o.1
    @12
    @14
    caddc
    ovex
    fnmpt2i
    @11
    vz
    @0
    @4
    @0
    wcel
    #
    @5
    @4
    c1st
    cfv
    #
    ci
    @4
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cc
    @16
    @5
    @17
    @18
    cF
    co
    #
    @20
    @16
    @5
    @17
    @18
    cop
    #
    cF
    cfv
    @21
    @16
    @4
    @22
    cF
    @4
    cr
    cr
    1st2nd2
    #
    fveq2d
    @17
    @18
    cF
    df-ov
    syl6eqr
    @16
    @17
    cr
    wcel
    #
    @18
    cr
    wcel
    #
    @21
    @20
    wceq
    @4
    cr
    cr
    xp1st
    #
    @4
    cr
    cr
    xp2nd
    #
    vx
    vy
    @17
    @18
    cr
    cr
    @15
    @20
    cF
    @17
    @14
    caddc
    co
    @12
    @17
    @14
    caddc
    oveq1
    @13
    @18
    wceq
    @14
    @19
    @17
    caddc
    @13
    @18
    ci
    cmul
    oveq2
    oveq2d
    cnref1o.1
    @17
    @19
    caddc
    ovex
    ovmpt2
    syl2anc
    eqtrd
    #
    @16
    @17
    @19
    @16
    @17
    @26
    recnd
    @16
    ci
    cc
    wcel
    @18
    cc
    wcel
    @19
    cc
    wcel
    ax-icn
    @16
    @18
    @27
    recnd
    ci
    @18
    mulcl
    sylancr
    addcld
    eqeltrd
    rgen
    vz
    @0
    cc
    cF
    ffnfv
    mpbir2an
    #
    @10
    vz
    vw
    @0
    @16
    @6
    @0
    wcel
    #
    wa
    #
    @8
    @9
    @31
    @20
    @6
    c1st
    cfv
    #
    ci
    @6
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @17
    @32
    wceq
    @18
    @33
    wceq
    wa
    #
    @8
    @9
    @16
    @24
    @25
    wa
    @32
    cr
    wcel
    #
    @33
    cr
    wcel
    #
    wa
    @36
    @37
    wb
    @30
    @16
    @24
    @25
    @26
    @27
    jca
    @30
    @38
    @39
    @6
    cr
    cr
    xp1st
    @6
    cr
    cr
    xp2nd
    jca
    @17
    @18
    @32
    @33
    cru
    syl2an
    @16
    @30
    @5
    @20
    @7
    @35
    @28
    @5
    @20
    wceq
    @7
    @35
    wceq
    vz
    @6
    @0
    @9
    @5
    @7
    @20
    @35
    @4
    @6
    cF
    fveq2
    @9
    @17
    @32
    @19
    @34
    caddc
    @4
    @6
    c1st
    fveq2
    @9
    @18
    @33
    ci
    cmul
    @4
    @6
    c2nd
    fveq2
    oveq2d
    oveq12d
    eqeq12d
    @28
    vtoclga
    eqeqan12d
    @31
    @9
    @22
    @32
    @33
    cop
    #
    wceq
    @37
    @16
    @30
    @4
    @22
    @6
    @40
    @23
    @6
    cr
    cr
    1st2nd2
    eqeqan12d
    @17
    @18
    @32
    @33
    @4
    c1st
    fvex
    @4
    c2nd
    fvex
    opth
    syl6bb
    3bitr4d
    biimpd
    rgen2a
    vz
    vw
    @0
    cc
    cF
    dff13
    mpbir2an
    @2
    @3
    @6
    @5
    wceq
    #
    vz
    @0
    wrex
    #
    vw
    cc
    wral
    @29
    @42
    vw
    cc
    @6
    cc
    wcel
    #
    @6
    vu
    cv
    #
    vv
    cv
    #
    cF
    co
    #
    wceq
    #
    vv
    cr
    wrex
    vu
    cr
    wrex
    #
    @42
    @43
    @6
    @44
    ci
    @45
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vv
    cr
    wrex
    vu
    cr
    wrex
    @48
    vu
    vv
    @6
    cnre
    @47
    @51
    vu
    vv
    cr
    cr
    @44
    cr
    wcel
    @45
    cr
    wcel
    wa
    @46
    @50
    @6
    vx
    vy
    @44
    @45
    cr
    cr
    @15
    @50
    cF
    @44
    @14
    caddc
    co
    @12
    @44
    @14
    caddc
    oveq1
    @13
    @45
    wceq
    @14
    @49
    @44
    caddc
    @13
    @45
    ci
    cmul
    oveq2
    oveq2d
    cnref1o.1
    @44
    @49
    caddc
    ovex
    ovmpt2
    eqeq2d
    2rexbiia
    sylibr
    @41
    @47
    vz
    vu
    vv
    cr
    cr
    @4
    @44
    @45
    cop
    #
    wceq
    #
    @5
    @46
    @6
    @53
    @5
    @52
    cF
    cfv
    @46
    @4
    @52
    cF
    fveq2
    @44
    @45
    cF
    df-ov
    syl6eqr
    eqeq2d
    rexxp
    sylibr
    rgen
    vz
    vw
    @0
    cc
    cF
    dffo3
    mpbir2an
    @0
    cc
    cF
    df-f1o
    mpbir2an
end

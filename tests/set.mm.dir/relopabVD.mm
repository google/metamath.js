include "copab.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "vex.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "ssopab2i.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "biantru.mm"
include "exbii.mm"
include "abbii.mm"
include "wi.mm"
include "ax6ev.mm"
include "equcom.mm"
include "mpbi.mm"
include "idn1.mm"
include "opeq2.mm"
include "e1a.mm"
include "idn2.mm"
include "opeq1.mm"
include "e2.mm"
include "eqeq1.mm"
include "biimprd.mm"
include "e12.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "in2.mm"
include "in1.mm"
include "eximi.mm"
include "ax-mp.mm"
include "19.37iv.mm"
include "19.37v.mm"
include "biimpi.mm"
include "syl.mm"
include "19.9v.mm"
include "ss2abi.mm"
include "eqsstr3i.mm"
include "sseqtri.mm"
include "df-opab.mm"
include "3sstr4i.mm"
include "df-xp.mm"
include "eqcomi.mm"
include "sstri.mm"
include "df-rel.mm"
include "biimpri.mm"
include "e0a.mm"

theorem relopabVD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v


  assert |- Rel { <. x , y >. | ph }

  proof
    wph
    vx
    vy
    copab
    #
    cvv
    cvv
    cxp
    #
    wss
    #
    @0
    wrel
    #
    @0
    vx
    cv
    #
    cvv
    wcel
    #
    vy
    cv
    #
    cvv
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    @1
    wph
    @8
    vx
    vy
    @8
    wph
    @5
    @7
    vx
    vex
    vy
    vex
    pm3.2i
    #
    a1i
    ssopab2i
    @9
    vu
    cv
    #
    cvv
    wcel
    #
    vv
    cv
    #
    cvv
    wcel
    #
    wa
    #
    vu
    vv
    copab
    #
    @1
    vz
    cv
    #
    @4
    @6
    cop
    #
    wceq
    #
    @8
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    #
    @17
    @11
    @13
    cop
    #
    wceq
    #
    @15
    wa
    #
    vv
    wex
    #
    vu
    wex
    #
    vz
    cab
    #
    @9
    @16
    @23
    @25
    vv
    wex
    #
    vu
    wex
    #
    vz
    cab
    #
    @29
    @23
    @19
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    @32
    @34
    @22
    vz
    @33
    @21
    vx
    @19
    @20
    vy
    @8
    @19
    @10
    biantru
    exbii
    exbii
    abbii
    @34
    @31
    vz
    @34
    @31
    vx
    wex
    #
    @31
    @33
    @31
    vx
    @33
    @31
    vy
    wex
    #
    @31
    @19
    @31
    vy
    @19
    @30
    vu
    @4
    @11
    wceq
    #
    vu
    wex
    #
    @19
    @30
    wi
    #
    vu
    wex
    @11
    @4
    wceq
    #
    vu
    wex
    @38
    vu
    vx
    ax6ev
    @40
    @37
    vu
    vu
    vx
    equcom
    exbii
    mpbi
    @37
    @39
    vu
    @37
    @19
    @25
    wi
    #
    vv
    wex
    #
    @39
    @37
    @41
    vv
    @6
    @13
    wceq
    #
    vv
    wex
    #
    @37
    @41
    wi
    #
    vv
    wex
    @13
    @6
    wceq
    #
    vv
    wex
    @44
    vv
    vy
    ax6ev
    @46
    @43
    vv
    vv
    vy
    equcom
    exbii
    mpbi
    @43
    @45
    vv
    @43
    @45
    @43
    @37
    @41
    @43
    @37
    @18
    @24
    wceq
    #
    @41
    @43
    @18
    @4
    @13
    cop
    #
    wceq
    #
    @37
    @48
    @24
    wceq
    #
    @47
    @43
    @43
    @49
    @43
    idn1
    @6
    @13
    @4
    opeq2
    e1a
    @43
    @37
    @37
    @50
    @43
    @37
    idn2
    @4
    @11
    @13
    opeq1
    e2
    @49
    @47
    @50
    @18
    @48
    @24
    eqeq1
    biimprd
    e12
    @47
    @19
    @25
    @18
    @24
    @17
    eqeq2
    biimpd
    e2
    in2
    in1
    eximi
    ax-mp
    19.37iv
    @42
    @39
    @19
    @25
    vv
    19.37v
    biimpi
    syl
    eximi
    ax-mp
    19.37iv
    eximi
    @36
    @31
    @31
    vy
    19.9v
    biimpi
    syl
    eximi
    @35
    @31
    @31
    vx
    19.9v
    biimpi
    syl
    ss2abi
    eqsstr3i
    @31
    @28
    vz
    @30
    @27
    vu
    @25
    @26
    vv
    @15
    @25
    @12
    @14
    vu
    vex
    vv
    vex
    pm3.2i
    biantru
    exbii
    exbii
    abbii
    sseqtri
    @8
    vx
    vy
    vz
    df-opab
    @15
    vu
    vv
    vz
    df-opab
    3sstr4i
    @1
    @16
    vu
    vv
    cvv
    cvv
    df-xp
    eqcomi
    sseqtri
    sstri
    @3
    @2
    @0
    df-rel
    biimpri
    e0a
end

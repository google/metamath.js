include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "citg1.mm"
include "wceq.mm"
include "c0.mm"
include "wi.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "covol.mm"
include "ovol0.mm"
include "0mbl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "itg10.mm"
include "3eqtr4ri.mm"
include "cv.mm"
include "c1.mm"
include "cif.mm"
include "cmpt.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "iffalsed.mm"
include "mpteq2dv.mm"
include "fconstmpt.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "3eqtr4a.mm"
include "a1i.mm"
include "wne.mm"
include "wex.mm"
include "n0.mm"
include "crn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cmul.mm"
include "co.mm"
include "csu.mm"
include "i1f1.mm"
include "adantr.mm"
include "itg1val.mm"
include "syl.mm"
include "wss.mm"
include "cpr.mm"
include "wf.mm"
include "i1f1lem.mm"
include "simpli.mm"
include "frn.mm"
include "ssdif.mm"
include "difprsnss.mm"
include "sstri.mm"
include "mblss.mm"
include "sselda.mm"
include "eleq1.mm"
include "ifbid.mm"
include "1ex.mm"
include "c0ex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtrd.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "ax-1ne0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "snssd.mm"
include "eqssd.mm"
include "sumeq1d.mm"
include "cc.mm"
include "1re.mm"
include "simpri.mm"
include "ad2antrr.mm"
include "oveq2d.mm"
include "simplr.mm"
include "recnd.mm"
include "mulid2d.mm"
include "eqeltrd.mm"
include "id.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "oveq12d.mm"
include "sumsn.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"

theorem itg11
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  assume i1f1.1: |- F = ( x e. RR |-> if ( x e. A , 1 , 0 ) )

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint y z
  disjoint F y
  disjoint F z
  assert |- ( ( A e. dom vol /\ ( vol ` A ) e. RR ) -> ( S.1 ` F ) = ( vol ` A ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    cF
    citg1
    cfv
    #
    @2
    wceq
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @6
    wi
    @4
    @7
    cr
    cc0
    csn
    #
    cxp
    #
    citg1
    cfv
    #
    c0
    cvol
    cfv
    #
    @5
    @2
    c0
    covol
    cfv
    #
    cc0
    @11
    @10
    ovol0
    c0
    @0
    wcel
    @11
    @12
    wceq
    0mbl
    c0
    mblvol
    ax-mp
    itg10
    3eqtr4ri
    @7
    cF
    @9
    citg1
    @7
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    c1
    cc0
    cif
    #
    cmpt
    vx
    cr
    cc0
    cmpt
    cF
    @9
    @7
    vx
    cr
    @15
    cc0
    @7
    @14
    c1
    cc0
    @7
    @14
    @13
    c0
    wcel
    @13
    noel
    cA
    c0
    @13
    eleq2
    mtbiri
    iffalsed
    mpteq2dv
    i1f1.1
    vx
    cr
    cc0
    fconstmpt
    3eqtr4g
    fveq2d
    cA
    c0
    cvol
    fveq2
    3eqtr4a
    a1i
    cA
    c0
    wne
    vy
    cv
    #
    cA
    wcel
    #
    vy
    wex
    @4
    @6
    vy
    cA
    n0
    @4
    @17
    @6
    vy
    @4
    @17
    @6
    @4
    @17
    wa
    #
    @5
    cF
    crn
    #
    @8
    cdif
    #
    vz
    cv
    #
    cF
    ccnv
    #
    @21
    csn
    #
    cima
    #
    cvol
    cfv
    #
    cmul
    co
    #
    vz
    csu
    #
    @2
    @18
    cF
    citg1
    cdm
    wcel
    #
    @5
    @27
    wceq
    @4
    @28
    @17
    vx
    cA
    cF
    i1f1.1
    i1f1
    adantr
    vz
    cF
    itg1val
    syl
    @18
    @27
    c1
    csn
    #
    @26
    vz
    csu
    #
    @2
    @18
    @20
    @29
    @26
    vz
    @18
    @20
    @29
    @20
    @29
    wss
    @18
    @20
    cc0
    c1
    cpr
    #
    @8
    cdif
    #
    @29
    @19
    @31
    wss
    #
    @20
    @32
    wss
    cr
    @31
    cF
    wf
    #
    @33
    @34
    @1
    @22
    @29
    cima
    #
    cA
    wceq
    #
    wi
    #
    vx
    cA
    cF
    i1f1.1
    i1f1lem
    #
    simpli
    #
    cr
    @31
    cF
    frn
    ax-mp
    @19
    @31
    @8
    ssdif
    ax-mp
    cc0
    c1
    difprsnss
    sstri
    a1i
    @18
    c1
    @20
    @18
    c1
    @19
    wcel
    c1
    cc0
    wne
    #
    c1
    @20
    wcel
    @18
    @16
    cF
    cfv
    #
    c1
    @19
    @18
    @41
    @17
    c1
    cc0
    cif
    #
    c1
    @18
    @16
    cr
    wcel
    #
    @41
    @42
    wceq
    @4
    cA
    cr
    @16
    @1
    cA
    cr
    wss
    @3
    cA
    mblss
    adantr
    sselda
    #
    vx
    @16
    @15
    @42
    cr
    cF
    @13
    @16
    wceq
    @14
    @17
    c1
    cc0
    @13
    @16
    cA
    eleq1
    ifbid
    i1f1.1
    @17
    c1
    cc0
    1ex
    c0ex
    ifex
    fvmpt
    syl
    @17
    @42
    c1
    wceq
    @4
    @17
    c1
    cc0
    iftrue
    adantl
    eqtrd
    @18
    cF
    cr
    wfn
    #
    @43
    @41
    @19
    wcel
    @34
    @45
    @39
    cr
    @31
    cF
    ffn
    ax-mp
    @44
    cr
    @16
    cF
    fnfvelrn
    sylancr
    eqeltrrd
    @40
    @18
    ax-1ne0
    a1i
    c1
    @19
    cc0
    eldifsn
    sylanbrc
    snssd
    eqssd
    sumeq1d
    @18
    @30
    c1
    @35
    cvol
    cfv
    #
    cmul
    co
    #
    @2
    @18
    c1
    cr
    wcel
    @47
    cc
    wcel
    @30
    @47
    wceq
    1re
    @18
    @47
    @2
    cc
    @18
    @47
    c1
    @2
    cmul
    co
    @2
    @18
    @46
    @2
    c1
    cmul
    @18
    @35
    cA
    cvol
    @1
    @36
    @3
    @17
    @34
    @37
    @38
    simpri
    ad2antrr
    fveq2d
    oveq2d
    @18
    @2
    @18
    @2
    @1
    @3
    @17
    simplr
    recnd
    #
    mulid2d
    eqtrd
    #
    @48
    eqeltrd
    @26
    @47
    vz
    c1
    cr
    @21
    c1
    wceq
    #
    @21
    c1
    @25
    @46
    cmul
    @50
    id
    @50
    @24
    @35
    cvol
    @50
    @23
    @29
    @22
    @21
    c1
    sneq
    imaeq2d
    fveq2d
    oveq12d
    sumsn
    sylancr
    @49
    eqtrd
    eqtrd
    eqtrd
    ex
    exlimdv
    syl5bi
    pm2.61dne
end

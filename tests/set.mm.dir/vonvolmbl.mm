include "cv.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "covoln.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "wceq.mm"
include "cr.mm"
include "cpw.mm"
include "wral.mm"
include "covol.mm"
include "cvoln.mm"
include "cdm.mm"
include "wcel.mm"
include "cvol.mm"
include "wa.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "reex.mm"
include "ssexd.mm"
include "cfn.mm"
include "snfi.mm"
include "elexd.mm"
include "inmap.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "difmapsn.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "ovexd.mm"
include "wss.mm"
include "elpwi.mm"
include "mapss.mm"
include "syl2anc.mm"
include "elpwd.mm"
include "adantl.mm"
include "simpl.mm"
include "ineq1.mm"
include "difeq1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "adantll.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "adantr.mm"
include "ovnovol.mm"
include "adantlr.mm"
include "ssinss1d.mm"
include "ssdifssd.mm"
include "3eqtr3d.mm"
include "ralrimiva.mm"
include "ex.mm"
include "crn.mm"
include "ciun.mm"
include "simplr.mm"
include "rneq.mm"
include "cbviunv.mm"
include "vonvolmbllem.mm"
include "impbid.mm"
include "isvonmbl.mm"
include "mpbirand.mm"
include "wb.mm"
include "ismbl4.mm"
include "3bitr4d.mm"

theorem vonvolmbl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  let vk: setvar k
  assume vonvolmbl.a: |- ( ph -> A e. V )
  assume vonvolmbl.b: |- ( ph -> B C_ RR )


  assert |- ( ph -> ( ( B ^m { A } ) e. dom ( voln ` { A } ) <-> B e. dom vol ) )

  proof
    wph
    vx
    cv
    #
    cB
    cA
    csn
    #
    cmap
    co
    #
    cin
    #
    @1
    covoln
    cfv
    #
    cfv
    #
    @0
    @2
    cdif
    #
    @4
    cfv
    #
    cxad
    co
    #
    @0
    @4
    cfv
    #
    wceq
    #
    vx
    cr
    @1
    cmap
    co
    #
    cpw
    #
    wral
    #
    vy
    cv
    #
    covol
    cfv
    #
    @14
    cB
    cin
    #
    covol
    cfv
    #
    @14
    cB
    cdif
    #
    covol
    cfv
    #
    cxad
    co
    #
    wceq
    #
    vy
    cr
    cpw
    #
    wral
    #
    @2
    @1
    cvoln
    cfv
    cdm
    wcel
    #
    cB
    cvol
    cdm
    wcel
    #
    wph
    @13
    @23
    wph
    @13
    @23
    wph
    @13
    wa
    #
    @21
    vy
    @22
    @26
    @14
    @22
    wcel
    #
    wa
    #
    @14
    @1
    cmap
    co
    #
    @4
    cfv
    #
    @16
    @1
    cmap
    co
    #
    @4
    cfv
    #
    @18
    @1
    cmap
    co
    #
    @4
    cfv
    #
    cxad
    co
    #
    @15
    @20
    @28
    @35
    @30
    @28
    @35
    @29
    @2
    cin
    #
    @4
    cfv
    #
    @29
    @2
    cdif
    #
    @4
    cfv
    #
    cxad
    co
    #
    @30
    @30
    wph
    @35
    @40
    wceq
    @13
    @27
    wph
    @32
    @37
    @34
    @39
    cxad
    wph
    @31
    @36
    @4
    wph
    @36
    @31
    wph
    @14
    cB
    @1
    cvv
    cvv
    cvv
    @14
    cvv
    wcel
    wph
    vy
    vex
    a1i
    #
    wph
    cB
    cr
    cvv
    cr
    cvv
    wcel
    #
    wph
    reex
    a1i
    #
    vonvolmbl.b
    ssexd
    #
    wph
    @1
    cfn
    @1
    cfn
    wcel
    wph
    cA
    snfi
    a1i
    #
    elexd
    inmap
    eqcomd
    fveq2d
    wph
    @33
    @38
    @4
    wph
    @38
    @33
    wph
    @14
    cB
    cA
    cvv
    cvv
    cV
    @41
    @44
    vonvolmbl.a
    difmapsn
    eqcomd
    fveq2d
    oveq12d
    ad2antrr
    @13
    @27
    @40
    @30
    wceq
    #
    wph
    @13
    @27
    wa
    @29
    @12
    wcel
    #
    @13
    @46
    @27
    @47
    @13
    @27
    @29
    @11
    cvv
    @27
    @14
    @1
    cmap
    ovexd
    @27
    @42
    @14
    cr
    wss
    #
    @29
    @11
    wss
    @42
    @27
    reex
    a1i
    @14
    cr
    elpwi
    #
    @14
    cr
    @1
    cvv
    mapss
    syl2anc
    elpwd
    adantl
    @13
    @27
    simpl
    @10
    @46
    vx
    @29
    @12
    @0
    @29
    wceq
    #
    @8
    @40
    @9
    @30
    @50
    @5
    @37
    @7
    @39
    cxad
    @50
    @3
    @36
    @4
    @0
    @29
    @2
    ineq1
    fveq2d
    @50
    @6
    @38
    @4
    @0
    @29
    @2
    difeq1
    fveq2d
    oveq12d
    @0
    @29
    @4
    fveq2
    eqeq12d
    rspcva
    syl2anc
    adantll
    @28
    @30
    eqidd
    3eqtrd
    eqcomd
    wph
    @27
    @30
    @15
    wceq
    @13
    wph
    @27
    wa
    #
    cA
    @14
    cV
    wph
    cA
    cV
    wcel
    #
    @27
    vonvolmbl.a
    adantr
    #
    @27
    @48
    wph
    @49
    adantl
    #
    ovnovol
    adantlr
    wph
    @27
    @35
    @20
    wceq
    @13
    @51
    @32
    @17
    @34
    @19
    cxad
    @51
    cA
    @16
    cV
    @53
    @51
    @14
    cB
    cr
    @54
    ssinss1d
    ovnovol
    @51
    cA
    @18
    cV
    @53
    @51
    @14
    cr
    cB
    @54
    ssdifssd
    ovnovol
    oveq12d
    adantlr
    3eqtr3d
    ralrimiva
    ex
    wph
    @23
    @13
    wph
    @23
    wa
    #
    @10
    vx
    @12
    @55
    @0
    @12
    wcel
    #
    wa
    vy
    cA
    cB
    vf
    cV
    @0
    vg
    @0
    vg
    cv
    #
    crn
    #
    ciun
    wph
    @52
    @23
    @56
    vonvolmbl.a
    ad2antrr
    wph
    cB
    cr
    wss
    #
    @23
    @56
    vonvolmbl.b
    ad2antrr
    wph
    @23
    @56
    simplr
    @56
    @0
    @11
    wss
    @55
    @0
    @11
    elpwi
    adantl
    vg
    vf
    @0
    @58
    vf
    cv
    #
    crn
    @57
    @60
    rneq
    cbviunv
    vonvolmbllem
    ralrimiva
    ex
    impbid
    wph
    @24
    @2
    @11
    wss
    #
    @13
    wph
    @42
    @59
    @61
    @43
    vonvolmbl.b
    cB
    cr
    @1
    cvv
    mapss
    syl2anc
    wph
    @2
    @1
    vx
    @45
    isvonmbl
    mpbirand
    wph
    @25
    @59
    @23
    vonvolmbl.b
    @25
    @59
    @23
    wa
    wb
    wph
    vy
    cB
    ismbl4
    a1i
    mpbirand
    3bitr4d
end

include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "simpr.mm"
include "c0.mm"
include "wne.mm"
include "adantlr.mm"
include "choicefi.mm"
include "wn.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "csdm.mm"
include "adantr.mm"
include "isfinite2.mm"
include "con3i.mm"
include "adantl.mm"
include "jca.mm"
include "bren2.mm"
include "sylibr.mm"
include "wi.mm"
include "cvv.mm"
include "ctex.mm"
include "syl.mm"
include "wceq.mm"
include "breq1.mm"
include "raleq.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "ax-cc.mm"
include "vtoclg.mm"
include "sylc.mm"
include "cmpt.mm"
include "mptexd.mm"
include "fvex.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "ax-mp.mm"
include "a1i.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "id.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "rspa.mm"
include "adantll.mm"
include "eqeltrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "fneq1.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfeq.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "ralbid.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "exlimdv.mm"
include "mpd.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem axccdom
  let wph: wff ph
  let vz: setvar z
  let vf: setvar f
  let cX: class X
  let vg: setvar g
  let vx: setvar x
  assume axccdom.1: |- ( ph -> X ~<_ _om )
  assume axccdom.2: |- ( ( ph /\ z e. X ) -> z =/= (/) )

  disjoint X f
  disjoint X z
  disjoint f z
  disjoint ph z
  disjoint X g
  disjoint f g
  disjoint g z
  disjoint X x
  disjoint g x
  disjoint x z
  disjoint g ph
  assert |- ( ph -> E. f ( f Fn X /\ A. z e. X ( f ` z ) e. z ) )

  proof
    wph
    cX
    cfn
    wcel
    #
    vf
    cv
    #
    cX
    wfn
    #
    vz
    cv
    #
    @1
    cfv
    #
    @3
    wcel
    #
    vz
    cX
    wral
    #
    wa
    #
    vf
    wex
    #
    wph
    @0
    wa
    #
    vz
    cX
    @3
    vf
    cX
    wph
    @0
    simpr
    @9
    @3
    cX
    wcel
    #
    simpr
    wph
    @10
    @3
    c0
    wne
    #
    @0
    axccdom.2
    adantlr
    choicefi
    wph
    @0
    wn
    #
    cX
    com
    cen
    wbr
    #
    @8
    wph
    @12
    wa
    #
    cX
    com
    cdom
    wbr
    #
    cX
    com
    csdm
    wbr
    #
    wn
    #
    wa
    @13
    @14
    @15
    @17
    wph
    @15
    @12
    axccdom.1
    adantr
    @12
    @17
    wph
    @16
    @0
    cX
    isfinite2
    con3i
    adantl
    jca
    cX
    com
    bren2
    sylibr
    wph
    @13
    wa
    #
    @11
    @3
    vg
    cv
    #
    cfv
    #
    @3
    wcel
    #
    wi
    #
    vz
    cX
    wral
    #
    vg
    wex
    #
    @8
    @18
    cX
    cvv
    wcel
    #
    @13
    @24
    wph
    @25
    @13
    wph
    @15
    @25
    axccdom.1
    cX
    ctex
    syl
    #
    adantr
    wph
    @13
    simpr
    vx
    cv
    #
    com
    cen
    wbr
    #
    @22
    vz
    @27
    wral
    #
    vg
    wex
    #
    wi
    @13
    @24
    wi
    vx
    cX
    cvv
    @27
    cX
    wceq
    #
    @28
    @13
    @30
    @24
    @27
    cX
    com
    cen
    breq1
    @31
    @29
    @23
    vg
    @22
    vz
    @27
    cX
    raleq
    exbidv
    imbi12d
    vx
    vz
    vg
    ax-cc
    vtoclg
    sylc
    @18
    @23
    @8
    vg
    @18
    @23
    @8
    wph
    @23
    @8
    @13
    wph
    @23
    wa
    #
    vz
    cX
    @20
    cmpt
    #
    cvv
    wcel
    #
    @33
    cX
    wfn
    #
    @3
    @33
    cfv
    #
    @3
    wcel
    #
    vz
    cX
    wral
    #
    wa
    #
    @8
    wph
    @34
    @23
    wph
    vz
    cX
    @20
    cvv
    @26
    mptexd
    adantr
    @32
    @35
    @38
    @35
    @32
    @20
    cvv
    wcel
    #
    vz
    cX
    wral
    @35
    @40
    vz
    cX
    @3
    @19
    fvex
    #
    rgenw
    vz
    cX
    @20
    @33
    cvv
    @33
    eqid
    #
    fnmpt
    ax-mp
    a1i
    @32
    @37
    vz
    cX
    wph
    @23
    vz
    wph
    vz
    nfv
    @22
    vz
    cX
    nfra1
    nfan
    @32
    @10
    @37
    @32
    @10
    wa
    #
    @36
    @20
    @3
    @10
    @36
    @20
    wceq
    #
    @32
    @10
    @10
    @40
    @44
    @10
    id
    @40
    @10
    @41
    a1i
    vz
    cX
    @20
    cvv
    @33
    @42
    fvmpt2
    syl2anc
    adantl
    @43
    @22
    @11
    @21
    @23
    @10
    @22
    wph
    @22
    vz
    cX
    rspa
    adantll
    wph
    @10
    @11
    @23
    axccdom.2
    adantlr
    @22
    id
    sylc
    eqeltrd
    ex
    ralrimi
    jca
    @7
    @39
    vf
    @33
    cvv
    @1
    @33
    wceq
    #
    @2
    @35
    @6
    @38
    cX
    @1
    @33
    fneq1
    @45
    @5
    @37
    vz
    cX
    vz
    @1
    @33
    vz
    @1
    nfcv
    vz
    cX
    @20
    nfmpt1
    nfeq
    @45
    @4
    @36
    @3
    @3
    @1
    @33
    fveq1
    eleq1d
    ralbid
    anbi12d
    spcegv
    sylc
    adantlr
    ex
    exlimdv
    mpd
    syldan
    pm2.61dan
end

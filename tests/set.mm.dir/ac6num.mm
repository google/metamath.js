include "wcel.mm"
include "crab.mm"
include "ciun.mm"
include "ccrd.mm"
include "cdm.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wa.mm"
include "wex.mm"
include "c0.mm"
include "wn.mm"
include "wceq.mm"
include "cab.mm"
include "cvv.mm"
include "nfiu1.mm"
include "nfel1.mm"
include "wss.mm"
include "ssiun2.mm"
include "ssexg.mm"
include "expcom.mm"
include "syl5.mm"
include "ralrimi.mm"
include "dfiun2g.mm"
include "syl.mm"
include "eqid.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "syl6eqr.mm"
include "id.mm"
include "eqeltrrd.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "wne.mm"
include "necom.mm"
include "rabn0.mm"
include "df-ne.mm"
include "3bitr3i.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "sylib.mm"
include "wb.mm"
include "0ex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylnibr.mm"
include "ac5num.mm"
include "syl2anc.mm"
include "wfn.mm"
include "ffn.mm"
include "anim1i.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "ralrnmpt.mm"
include "anbi2d.mm"
include "syl5ib.mm"
include "wsbc.mm"
include "csb.mm"
include "sseld.mm"
include "ralimia.mm"
include "ad2antll.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "fmpt.mm"
include "simpl1.mm"
include "simpl2.mm"
include "fex2.mm"
include "syl3anc.mm"
include "ssrab2.mm"
include "sseli.mm"
include "ralimi.mm"
include "elrabsf.mm"
include "simprbi.mm"
include "jca.mm"
include "feq1.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "fvex.mm"
include "sbcie.mm"
include "fveq1.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "sylan9eq.mm"
include "sbceq1d.mm"
include "syl5bbr.mm"
include "ralbida.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "ex.mm"
include "syld.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem ac6num
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cV: class V
  let vg: setvar g
  let vz: setvar z
  assume ac6num.1: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f ph
  disjoint ps y
  disjoint f g
  disjoint f z
  disjoint g x
  disjoint g z
  disjoint A g
  disjoint x z
  disjoint A z
  disjoint g y
  disjoint B g
  disjoint y z
  disjoint B z
  disjoint g ph
  disjoint ph z
  disjoint g ps
  disjoint V g
  assert |- ( ( A e. V /\ U_ x e. A { y e. B | ph } e. dom card /\ A. x e. A E. y e. B ph ) -> E. f ( f : A --> B /\ A. x e. A ps ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    wph
    vy
    cB
    crab
    #
    ciun
    #
    ccrd
    cdm
    #
    wcel
    #
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    w3a
    #
    vx
    cA
    @1
    cmpt
    #
    crn
    #
    @9
    cuni
    #
    vg
    cv
    #
    wf
    #
    vz
    cv
    #
    @11
    cfv
    #
    @13
    wcel
    #
    vz
    @9
    wral
    #
    wa
    #
    vg
    wex
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    wps
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    @7
    @10
    @3
    wcel
    #
    c0
    @9
    wcel
    #
    wn
    @18
    @4
    @0
    @24
    @6
    @4
    @2
    @10
    @3
    @4
    @2
    @13
    @1
    wceq
    #
    vx
    cA
    wrex
    vz
    cab
    #
    cuni
    #
    @10
    @4
    @1
    cvv
    wcel
    #
    vx
    cA
    wral
    #
    @2
    @28
    wceq
    @4
    @29
    vx
    cA
    vx
    @2
    @3
    vx
    cA
    @1
    nfiu1
    #
    nfel1
    vx
    cv
    #
    cA
    wcel
    #
    @1
    @2
    wss
    #
    @4
    @29
    vx
    cA
    @1
    ssiun2
    #
    @34
    @4
    @29
    @1
    @2
    @3
    ssexg
    expcom
    syl5
    ralrimi
    #
    vx
    vz
    cA
    @1
    cvv
    dfiun2g
    syl
    @9
    @27
    vx
    vz
    cA
    @1
    @8
    @8
    eqid
    #
    rnmpt
    unieqi
    syl6eqr
    @4
    id
    eqeltrrd
    3ad2ant2
    @7
    c0
    @1
    wceq
    #
    vx
    cA
    wrex
    #
    @25
    @7
    @6
    @39
    wn
    #
    @0
    @4
    @6
    simp3
    @6
    @38
    wn
    #
    vx
    cA
    wral
    @40
    @5
    @41
    vx
    cA
    @1
    c0
    wne
    c0
    @1
    wne
    @5
    @41
    @1
    c0
    necom
    wph
    vy
    cB
    rabn0
    c0
    @1
    df-ne
    3bitr3i
    ralbii
    @38
    vx
    cA
    ralnex
    bitri
    sylib
    c0
    cvv
    wcel
    @25
    @39
    wb
    0ex
    vx
    cA
    @1
    c0
    @8
    cvv
    @37
    elrnmpt
    ax-mp
    sylnibr
    vz
    @9
    vg
    ac5num
    syl2anc
    @7
    @17
    @23
    vg
    @7
    @17
    @11
    @9
    wfn
    #
    @1
    @11
    cfv
    #
    @1
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @23
    @17
    @42
    @16
    wa
    @7
    @46
    @12
    @42
    @16
    @9
    @10
    @11
    ffn
    anim1i
    @7
    @16
    @45
    @42
    @7
    @30
    @16
    @45
    wb
    @4
    @0
    @30
    @6
    @36
    3ad2ant2
    @15
    @44
    vx
    vz
    cA
    @1
    @8
    cvv
    @37
    @26
    @14
    @43
    @13
    @1
    @13
    @1
    @11
    fveq2
    @26
    id
    eleq12d
    ralrnmpt
    syl
    anbi2d
    syl5ib
    @7
    @46
    @23
    @7
    @46
    wa
    #
    vx
    cA
    @43
    cmpt
    #
    cvv
    wcel
    #
    cA
    cB
    @48
    wf
    #
    wph
    vy
    @43
    wsbc
    #
    vx
    cA
    wral
    #
    wa
    #
    @23
    @47
    cA
    @2
    @48
    wf
    #
    @0
    @4
    @49
    @47
    vx
    @13
    @43
    csb
    #
    @2
    wcel
    #
    vz
    cA
    wral
    #
    @54
    @47
    @43
    @2
    wcel
    #
    vx
    cA
    wral
    #
    @57
    @45
    @59
    @7
    @42
    @44
    @58
    vx
    cA
    @33
    @1
    @2
    @43
    @35
    sseld
    ralimia
    ad2antll
    @58
    @56
    vx
    vz
    cA
    @58
    vz
    nfv
    vx
    @55
    @2
    vx
    @13
    @43
    nfcsb1v
    #
    @31
    nfel
    @32
    @13
    wceq
    @43
    @55
    @2
    vx
    @13
    @43
    csbeq1a
    #
    eleq1d
    cbvral
    sylib
    vz
    cA
    @2
    @55
    @48
    vx
    vz
    cA
    @43
    @55
    vz
    @43
    nfcv
    @60
    @61
    cbvmpt
    fmpt
    sylib
    @0
    @4
    @6
    @46
    simpl1
    @0
    @4
    @6
    @46
    simpl2
    cA
    @2
    @48
    cV
    @3
    fex2
    syl3anc
    @47
    @50
    @52
    @47
    @43
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @50
    @45
    @63
    @7
    @42
    @44
    @62
    vx
    cA
    @1
    cB
    @43
    wph
    vy
    cB
    ssrab2
    sseli
    ralimi
    ad2antll
    vx
    cA
    cB
    @43
    @48
    @48
    eqid
    #
    fmpt
    sylib
    @45
    @52
    @7
    @42
    @44
    @51
    vx
    cA
    @44
    @62
    @51
    wph
    vy
    @43
    cB
    vy
    cB
    nfcv
    elrabsf
    simprbi
    ralimi
    ad2antll
    jca
    @22
    @53
    vf
    @48
    cvv
    @19
    @48
    wceq
    #
    @20
    @50
    @21
    @52
    cA
    cB
    @19
    @48
    feq1
    @65
    wps
    @51
    vx
    cA
    vx
    @19
    @48
    vx
    cA
    @43
    nfmpt1
    nfeq2
    wps
    wph
    vy
    @32
    @19
    cfv
    #
    wsbc
    @65
    @33
    wa
    #
    @51
    wph
    wps
    vy
    @66
    @32
    @19
    fvex
    ac6num.1
    sbcie
    @67
    wph
    vy
    @66
    @43
    @65
    @33
    @66
    @32
    @48
    cfv
    #
    @43
    @32
    @19
    @48
    fveq1
    @33
    @43
    cvv
    wcel
    @68
    @43
    wceq
    @1
    @11
    fvex
    vx
    cA
    @43
    cvv
    @48
    @64
    fvmpt2
    mpan2
    sylan9eq
    sbceq1d
    syl5bbr
    ralbida
    anbi12d
    spcegv
    sylc
    ex
    syld
    exlimdv
    mpd
end

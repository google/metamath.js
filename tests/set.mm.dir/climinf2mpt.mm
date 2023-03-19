include "cmpt.mm"
include "nfv.mm"
include "nfcv.mm"
include "cr.mm"
include "fmptd2f.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "csb.mm"
include "wi.mm"
include "nfan.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "csbeq1d.mm"
include "eqidd.mm"
include "csbco.mm"
include "csbid.mm"
include "eqtr2i.mm"
include "cbvcsb.mm"
include "eqtri.mm"
include "csbeq2i.mm"
include "a1i.mm"
include "csbeq1.mm"
include "3eqtrd.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "simpl.mm"
include "simpr.mm"
include "w3a.mm"
include "nf3an.mm"
include "nfcsb1v.mm"
include "nfbr.mm"
include "ovex.mm"
include "eqeq1.mm"
include "3anbi3d.mm"
include "csbeq1a.mm"
include "breq1d.mm"
include "vtoclf.mm"
include "syl3anc.mm"
include "chvar.mm"
include "eqcomi.mm"
include "mpbird.mm"
include "peano2uzs.mm"
include "adantl.mm"
include "nfcsb1.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "sylan2.mm"
include "eqid.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "nfel.mm"
include "wral.mm"
include "wrex.mm"
include "cabs.mm"
include "cz.mm"
include "cli.mm"
include "cdm.mm"
include "cc.mm"
include "eqeltrd.mm"
include "recnd.mm"
include "ralrimiva.mm"
include "climbddf.mm"
include "rexabsle2.mm"
include "mpbid.mm"
include "simprd.mm"
include "climinf2.mm"

theorem climinf2mpt
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vx: setvar x
  assume climinf2mpt.p: |- F/ k ph
  assume climinf2mpt.j: |- F/ j ph
  assume climinf2mpt.m: |- ( ph -> M e. ZZ )
  assume climinf2mpt.z: |- Z = ( ZZ>= ` M )
  assume climinf2mpt.b: |- ( ( ph /\ k e. Z ) -> B e. RR )
  assume climinf2mpt.c: |- ( k = j -> B = C )
  assume climinf2mpt.l: |- ( ( ph /\ k e. Z /\ j = ( k + 1 ) ) -> C <_ B )
  assume climinf2mpt.e: |- ( ph -> ( k e. Z |-> B ) e. dom ~~> )

  disjoint B j
  disjoint C k
  disjoint Z j
  disjoint Z k
  disjoint j k
  disjoint B i
  disjoint i j
  disjoint B x
  disjoint i x
  disjoint M i
  disjoint M x
  disjoint Z i
  disjoint i k
  disjoint Z x
  disjoint k x
  disjoint i ph
  assert |- ( ph -> ( k e. Z |-> B ) ~~> inf ( ran ( k e. Z |-> B ) , RR* , < ) )

  proof
    wph
    vx
    vi
    vk
    cZ
    cB
    cmpt
    #
    cM
    cZ
    wph
    vi
    nfv
    #
    vi
    @0
    nfcv
    #
    climinf2mpt.z
    climinf2mpt.m
    wph
    vk
    cZ
    cB
    cr
    climinf2mpt.p
    climinf2mpt.b
    fmptd2f
    wph
    vi
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @3
    c1
    caddc
    co
    #
    @0
    cfv
    #
    @3
    @0
    cfv
    #
    cle
    wbr
    vk
    @6
    cB
    csb
    #
    vj
    @3
    cC
    csb
    #
    cle
    wbr
    #
    @5
    @11
    vj
    @6
    cC
    csb
    #
    @10
    cle
    wbr
    #
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    vj
    @14
    c1
    caddc
    co
    #
    cC
    csb
    #
    cB
    cle
    wbr
    #
    wi
    @5
    @13
    wi
    vk
    vi
    @5
    @13
    vk
    wph
    @4
    vk
    climinf2mpt.p
    @4
    vk
    nfv
    nfan
    @13
    vk
    nfv
    nfim
    @14
    @3
    wceq
    #
    @16
    @5
    @19
    @13
    @20
    @15
    @4
    wph
    @14
    @3
    cZ
    eleq1
    anbi2d
    @20
    @18
    @12
    cB
    @10
    cle
    @20
    vj
    @17
    @6
    cC
    @14
    @3
    c1
    caddc
    oveq1
    csbeq1d
    @20
    cB
    cB
    vj
    @14
    cC
    csb
    #
    @10
    @20
    cB
    eqidd
    cB
    @21
    wceq
    @20
    cB
    vj
    @14
    vk
    vj
    cv
    #
    cB
    csb
    #
    csb
    #
    @21
    @24
    vk
    @14
    cB
    csb
    cB
    vk
    vj
    @14
    cB
    csbco
    vk
    cB
    csbid
    eqtr2i
    vj
    @14
    @23
    cC
    @23
    vj
    @22
    cC
    csb
    cC
    vk
    vj
    @22
    cB
    cC
    vj
    cB
    nfcv
    #
    vk
    cC
    nfcv
    climinf2mpt.c
    cbvcsb
    vj
    cC
    csbid
    eqtri
    #
    csbeq2i
    eqtri
    a1i
    vj
    @14
    @3
    cC
    csbeq1
    3eqtrd
    #
    breq12d
    imbi12d
    @16
    wph
    @15
    @17
    @17
    wceq
    #
    @19
    wph
    @15
    simpl
    wph
    @15
    simpr
    @16
    @17
    eqidd
    wph
    @15
    @22
    @17
    wceq
    #
    w3a
    #
    cC
    cB
    cle
    wbr
    #
    wi
    wph
    @15
    @28
    w3a
    #
    @19
    wi
    vj
    @17
    @32
    @19
    vj
    wph
    @15
    @28
    vj
    climinf2mpt.j
    @15
    vj
    nfv
    @28
    vj
    nfv
    nf3an
    vj
    @18
    cB
    cle
    vj
    @17
    cC
    nfcsb1v
    vj
    cle
    nfcv
    @25
    nfbr
    nfim
    @14
    c1
    caddc
    ovex
    @29
    @30
    @32
    @31
    @19
    @29
    @29
    @28
    wph
    @15
    @22
    @17
    @17
    eqeq1
    3anbi3d
    @29
    cC
    @18
    cB
    cle
    vj
    @17
    cC
    csbeq1a
    breq1d
    imbi12d
    climinf2mpt.l
    vtoclf
    syl3anc
    chvar
    @5
    @9
    @12
    @10
    @10
    cle
    @9
    @12
    wceq
    @5
    @9
    vj
    @6
    @23
    csb
    #
    @12
    @33
    @9
    vk
    vj
    @6
    cB
    csbco
    eqcomi
    vj
    @6
    @23
    cC
    @26
    csbeq2i
    eqtri
    a1i
    @5
    @10
    eqidd
    breq12d
    mpbird
    @5
    @7
    @9
    @8
    @10
    cle
    @5
    @6
    cZ
    wcel
    #
    @9
    cr
    wcel
    #
    @7
    @9
    wceq
    @4
    @34
    wph
    cM
    @3
    cZ
    climinf2mpt.z
    peano2uzs
    #
    adantl
    @4
    wph
    @34
    @35
    @36
    @16
    cB
    cr
    wcel
    #
    wi
    #
    wph
    @34
    wa
    #
    @35
    wi
    vk
    @6
    @39
    @35
    vk
    wph
    @34
    vk
    climinf2mpt.p
    @34
    vk
    nfv
    nfan
    vk
    @9
    cr
    vk
    @6
    cB
    vk
    @6
    nfcv
    #
    nfcsb1
    #
    nfel1
    nfim
    @3
    c1
    caddc
    ovex
    @14
    @6
    wceq
    #
    @16
    @39
    @37
    @35
    @42
    @15
    @34
    wph
    @14
    @6
    cZ
    eleq1
    anbi2d
    @42
    cB
    @9
    cr
    vk
    @6
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    climinf2mpt.b
    vtoclf
    sylan2
    vk
    @6
    cB
    @9
    cZ
    @0
    cr
    @40
    @41
    @43
    @0
    eqid
    #
    fvmptf
    syl2anc
    @5
    @4
    @10
    cr
    wcel
    #
    @8
    @10
    wceq
    wph
    @4
    simpr
    wph
    @22
    cZ
    wcel
    #
    wa
    #
    cC
    cr
    wcel
    #
    wi
    #
    @5
    @45
    wi
    vj
    vi
    @5
    @45
    vj
    wph
    @4
    vj
    climinf2mpt.j
    @4
    vj
    nfv
    nfan
    vj
    @10
    cr
    vj
    @3
    cC
    nfcsb1v
    vj
    cr
    nfcv
    nfel
    nfim
    @22
    @3
    wceq
    #
    @47
    @5
    @48
    @45
    @50
    @46
    @4
    wph
    @22
    @3
    cZ
    eleq1
    anbi2d
    @50
    cC
    @10
    cr
    vj
    @3
    cC
    csbeq1a
    eleq1d
    imbi12d
    @38
    @49
    vk
    vj
    @47
    @48
    vk
    wph
    @46
    vk
    climinf2mpt.p
    @46
    vk
    nfv
    nfan
    @48
    vk
    nfv
    nfim
    @14
    @22
    wceq
    #
    @16
    @47
    @37
    @48
    @51
    @15
    @46
    wph
    @14
    @22
    cZ
    eleq1
    anbi2d
    @51
    cB
    cC
    cr
    climinf2mpt.c
    eleq1d
    imbi12d
    climinf2mpt.b
    chvar
    chvar
    #
    vk
    @3
    cB
    @10
    cZ
    @0
    cr
    vk
    @3
    nfcv
    vk
    @10
    nfcv
    @27
    @44
    fvmptf
    syl2anc
    #
    breq12d
    mpbird
    wph
    @8
    vx
    cv
    #
    cle
    wbr
    vi
    cZ
    wral
    vx
    cr
    wrex
    #
    @54
    @8
    cle
    wbr
    vi
    cZ
    wral
    vx
    cr
    wrex
    #
    wph
    @8
    cabs
    cfv
    @54
    cle
    wbr
    vi
    cZ
    wral
    vx
    cr
    wrex
    #
    @55
    @56
    wa
    wph
    cM
    cz
    wcel
    @0
    cli
    cdm
    wcel
    @8
    cc
    wcel
    #
    vi
    cZ
    wral
    @57
    climinf2mpt.m
    climinf2mpt.e
    wph
    @58
    vi
    cZ
    @5
    @8
    @5
    @8
    @10
    cr
    @53
    @52
    eqeltrd
    #
    recnd
    ralrimiva
    vx
    vi
    @0
    cM
    cZ
    @2
    climinf2mpt.z
    climbddf
    syl3anc
    wph
    vi
    vx
    cZ
    @8
    @1
    @59
    rexabsle2
    mpbid
    simprd
    climinf2
end

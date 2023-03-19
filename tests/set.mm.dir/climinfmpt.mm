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
include "breq1.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "wb.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvral.mm"
include "fvmpt2d.mm"
include "ralbida.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "climinf2.mm"

theorem climinfmpt
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vy: setvar y
  assume climinfmpt.p: |- F/ k ph
  assume climinfmpt.j: |- F/ j ph
  assume climinfmpt.m: |- ( ph -> M e. ZZ )
  assume climinfmpt.z: |- Z = ( ZZ>= ` M )
  assume climinfmpt.b: |- ( ( ph /\ k e. Z ) -> B e. RR )
  assume climinfmpt.c: |- ( k = j -> B = C )
  assume climinfmpt.l: |- ( ( ph /\ k e. Z /\ j = ( k + 1 ) ) -> C <_ B )
  assume climinfmpt.e: |- ( ph -> E. x e. RR A. k e. Z x <_ B )

  disjoint B j
  disjoint B x
  disjoint C k
  disjoint Z j
  disjoint Z k
  disjoint j k
  disjoint Z x
  disjoint k x
  disjoint B i
  disjoint i j
  disjoint B y
  disjoint x y
  disjoint Z i
  disjoint i k
  disjoint Z y
  disjoint k y
  disjoint i ph
  disjoint i y
  disjoint ph y
  assert |- ( ph -> ( k e. Z |-> B ) ~~> inf ( ran ( k e. Z |-> B ) , RR* , < ) )

  proof
    wph
    vy
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
    vi
    @0
    nfcv
    climinfmpt.z
    climinfmpt.m
    wph
    vk
    cZ
    cB
    cr
    climinfmpt.p
    climinfmpt.b
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
    @1
    c1
    caddc
    co
    #
    @0
    cfv
    #
    @1
    @0
    cfv
    #
    cle
    wbr
    vk
    @4
    cB
    csb
    #
    vj
    @1
    cC
    csb
    #
    cle
    wbr
    #
    @3
    @9
    vj
    @4
    cC
    csb
    #
    @8
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
    @12
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
    @3
    @11
    wi
    vk
    vi
    @3
    @11
    vk
    wph
    @2
    vk
    climinfmpt.p
    @2
    vk
    nfv
    nfan
    @11
    vk
    nfv
    nfim
    @12
    @1
    wceq
    #
    @14
    @3
    @17
    @11
    @18
    @13
    @2
    wph
    @12
    @1
    cZ
    eleq1
    anbi2d
    @18
    @16
    @10
    cB
    @8
    cle
    @18
    vj
    @15
    @4
    cC
    @12
    @1
    c1
    caddc
    oveq1
    csbeq1d
    @18
    cB
    cB
    vj
    @12
    cC
    csb
    #
    @8
    @18
    cB
    eqidd
    cB
    @19
    wceq
    @18
    cB
    vj
    @12
    vk
    vj
    cv
    #
    cB
    csb
    #
    csb
    #
    @19
    @22
    vk
    @12
    cB
    csb
    cB
    vk
    vj
    @12
    cB
    csbco
    vk
    cB
    csbid
    eqtr2i
    vj
    @12
    @21
    cC
    @21
    vj
    @20
    cC
    csb
    cC
    vk
    vj
    @20
    cB
    cC
    vj
    cB
    nfcv
    #
    vk
    cC
    nfcv
    climinfmpt.c
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
    @12
    @1
    cC
    csbeq1
    3eqtrd
    #
    breq12d
    imbi12d
    @14
    wph
    @13
    @15
    @15
    wceq
    #
    @17
    wph
    @13
    simpl
    wph
    @13
    simpr
    @14
    @15
    eqidd
    wph
    @13
    @20
    @15
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
    @13
    @26
    w3a
    #
    @17
    wi
    vj
    @15
    @30
    @17
    vj
    wph
    @13
    @26
    vj
    climinfmpt.j
    @13
    vj
    nfv
    @26
    vj
    nfv
    nf3an
    vj
    @16
    cB
    cle
    vj
    @15
    cC
    nfcsb1v
    vj
    cle
    nfcv
    @23
    nfbr
    nfim
    @12
    c1
    caddc
    ovex
    @27
    @28
    @30
    @29
    @17
    @27
    @27
    @26
    wph
    @13
    @20
    @15
    @15
    eqeq1
    3anbi3d
    @27
    cC
    @16
    cB
    cle
    vj
    @15
    cC
    csbeq1a
    breq1d
    imbi12d
    climinfmpt.l
    vtoclf
    syl3anc
    chvar
    @3
    @7
    @10
    @8
    @8
    cle
    @7
    @10
    wceq
    @3
    @7
    vj
    @4
    @21
    csb
    #
    @10
    @31
    @7
    vk
    vj
    @4
    cB
    csbco
    eqcomi
    vj
    @4
    @21
    cC
    @24
    csbeq2i
    eqtri
    a1i
    @3
    @8
    eqidd
    breq12d
    mpbird
    @3
    @5
    @7
    @6
    @8
    cle
    @3
    @4
    cZ
    wcel
    #
    @7
    cr
    wcel
    #
    @5
    @7
    wceq
    @2
    @32
    wph
    cM
    @1
    cZ
    climinfmpt.z
    peano2uzs
    #
    adantl
    @2
    wph
    @32
    @33
    @34
    @14
    cB
    cr
    wcel
    #
    wi
    #
    wph
    @32
    wa
    #
    @33
    wi
    vk
    @4
    @37
    @33
    vk
    wph
    @32
    vk
    climinfmpt.p
    @32
    vk
    nfv
    nfan
    vk
    @7
    cr
    vk
    @4
    cB
    vk
    @4
    nfcv
    #
    nfcsb1
    #
    nfel1
    nfim
    @1
    c1
    caddc
    ovex
    @12
    @4
    wceq
    #
    @14
    @37
    @35
    @33
    @40
    @13
    @32
    wph
    @12
    @4
    cZ
    eleq1
    anbi2d
    @40
    cB
    @7
    cr
    vk
    @4
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    climinfmpt.b
    vtoclf
    sylan2
    vk
    @4
    cB
    @7
    cZ
    @0
    cr
    @38
    @39
    @41
    @0
    eqid
    #
    fvmptf
    syl2anc
    @3
    @2
    @8
    cr
    wcel
    #
    @6
    @8
    wceq
    wph
    @2
    simpr
    wph
    @20
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
    @3
    @43
    wi
    vj
    vi
    @3
    @43
    vj
    wph
    @2
    vj
    climinfmpt.j
    @2
    vj
    nfv
    nfan
    vj
    @8
    cr
    vj
    @1
    cC
    nfcsb1v
    vj
    cr
    nfcv
    nfel
    nfim
    @20
    @1
    wceq
    #
    @45
    @3
    @46
    @43
    @48
    @44
    @2
    wph
    @20
    @1
    cZ
    eleq1
    anbi2d
    @48
    cC
    @8
    cr
    vj
    @1
    cC
    csbeq1a
    eleq1d
    imbi12d
    @36
    @47
    vk
    vj
    @45
    @46
    vk
    wph
    @44
    vk
    climinfmpt.p
    @44
    vk
    nfv
    nfan
    @46
    vk
    nfv
    nfim
    @12
    @20
    wceq
    #
    @14
    @45
    @35
    @46
    @49
    @13
    @44
    wph
    @12
    @20
    cZ
    eleq1
    anbi2d
    @49
    cB
    cC
    cr
    climinfmpt.c
    eleq1d
    imbi12d
    climinfmpt.b
    chvar
    chvar
    vk
    @1
    cB
    @8
    cZ
    @0
    cr
    vk
    @1
    nfcv
    #
    vk
    @8
    nfcv
    @25
    @42
    fvmptf
    syl2anc
    breq12d
    mpbird
    wph
    vy
    cv
    #
    @6
    cle
    wbr
    #
    vi
    cZ
    wral
    #
    vy
    cr
    wrex
    @51
    cB
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    wph
    vx
    cv
    #
    cB
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    @56
    climinfmpt.e
    @59
    @55
    vx
    vy
    cr
    @57
    @51
    wceq
    @58
    @54
    vk
    cZ
    @57
    @51
    cB
    cle
    breq1
    ralbidv
    cbvrexv
    sylib
    wph
    @53
    @55
    vy
    cr
    wph
    @53
    @51
    @12
    @0
    cfv
    #
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    @55
    @53
    @62
    wb
    wph
    @52
    @61
    vi
    vk
    cZ
    vk
    @51
    @6
    cle
    vk
    @51
    nfcv
    vk
    cle
    nfcv
    vk
    @1
    @0
    vk
    cZ
    cB
    nfmpt1
    @50
    nffv
    nfbr
    @61
    vi
    nfv
    @1
    @12
    wceq
    @6
    @60
    @51
    cle
    @1
    @12
    @0
    fveq2
    breq2d
    cbvral
    a1i
    wph
    @61
    @54
    vk
    cZ
    climinfmpt.p
    @14
    @60
    cB
    @51
    cle
    wph
    vk
    cZ
    cB
    @0
    cr
    @0
    @0
    wceq
    wph
    @42
    a1i
    climinfmpt.b
    fvmpt2d
    breq2d
    ralbida
    bitrd
    rexbidv
    mpbird
    climinf2
end

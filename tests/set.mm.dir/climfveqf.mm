include "cli.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wbr.mm"
include "climdm.mm"
include "biimpi.mm"
include "adantl.mm"
include "sylibr.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfan.mm"
include "nffv.mm"
include "nfeq.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "climeldmeq.mm"
include "adantr.mm"
include "mpbid.mm"
include "sylib.mm"
include "cz.mm"
include "eqcomd.mm"
include "adantlr.mm"
include "climeq.mm"
include "climuni.mm"
include "syl2anc.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "simpr.mm"
include "mtbid.mm"
include "syl.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem climfveqf
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  assume climfveqf.p: |- F/ k ph
  assume climfveqf.n: |- F/_ k F
  assume climfveqf.o: |- F/_ k G
  assume climfveqf.z: |- Z = ( ZZ>= ` M )
  assume climfveqf.f: |- ( ph -> F e. V )
  assume climfveqf.g: |- ( ph -> G e. W )
  assume climfveqf.m: |- ( ph -> M e. ZZ )
  assume climfveqf.e: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` k ) )

  disjoint Z k
  disjoint F j
  disjoint G j
  disjoint Z j
  disjoint j k
  disjoint j ph
  assert |- ( ph -> ( ~~> ` F ) = ( ~~> ` G ) )

  proof
    wph
    cF
    cli
    cdm
    #
    wcel
    #
    cF
    cli
    cfv
    #
    cG
    cli
    cfv
    #
    wceq
    #
    wph
    @1
    wa
    #
    cF
    @2
    cli
    wbr
    #
    cF
    @3
    cli
    wbr
    #
    @4
    @1
    @6
    wph
    @1
    @6
    cF
    climdm
    #
    biimpi
    adantl
    #
    @5
    cG
    @3
    cli
    wbr
    #
    @7
    @5
    cG
    @0
    wcel
    #
    @10
    @5
    @1
    @11
    @5
    @6
    @1
    @9
    @8
    sylibr
    wph
    @1
    @11
    wb
    #
    @1
    wph
    vj
    cF
    cG
    cM
    cV
    cW
    cZ
    climfveqf.z
    climfveqf.f
    climfveqf.g
    climfveqf.m
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @13
    cF
    cfv
    #
    @13
    cG
    cfv
    #
    wceq
    #
    wi
    wph
    vj
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @19
    cF
    cfv
    #
    @19
    cG
    cfv
    #
    wceq
    #
    wi
    vk
    vj
    @21
    @24
    vk
    wph
    @20
    vk
    climfveqf.p
    vk
    @19
    cZ
    vk
    @19
    nfcv
    #
    nfel1
    nfan
    vk
    @22
    @23
    vk
    @19
    cF
    climfveqf.n
    @25
    nffv
    vk
    @19
    cG
    climfveqf.o
    @25
    nffv
    nfeq
    nfim
    @13
    @19
    wceq
    #
    @15
    @21
    @18
    @24
    @26
    @14
    @20
    wph
    @13
    @19
    cZ
    eleq1
    anbi2d
    @26
    @16
    @22
    @17
    @23
    @13
    @19
    cF
    fveq2
    @13
    @19
    cG
    fveq2
    eqeq12d
    imbi12d
    climfveqf.e
    chvar
    #
    climeldmeq
    #
    adantr
    mpbid
    cG
    climdm
    sylib
    @5
    @3
    vj
    cG
    cF
    cM
    cW
    cV
    cZ
    climfveqf.z
    wph
    cG
    cW
    wcel
    @1
    climfveqf.g
    adantr
    wph
    cF
    cV
    wcel
    @1
    climfveqf.f
    adantr
    wph
    cM
    cz
    wcel
    @1
    climfveqf.m
    adantr
    wph
    @20
    @23
    @22
    wceq
    @1
    @21
    @22
    @23
    @27
    eqcomd
    adantlr
    climeq
    mpbid
    @2
    @3
    cF
    climuni
    syl2anc
    wph
    @1
    wn
    #
    wa
    #
    @2
    c0
    @3
    @29
    @2
    c0
    wceq
    wph
    cF
    cli
    ndmfv
    adantl
    @30
    @11
    wn
    @3
    c0
    wceq
    @30
    @1
    @11
    wph
    @29
    simpr
    wph
    @12
    @29
    @28
    adantr
    mtbid
    cG
    cli
    ndmfv
    syl
    eqtr4d
    pm2.61dan
end

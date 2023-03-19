include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cc.mm"
include "cres.mm"
include "wf.mm"
include "clsxlim.mm"
include "wbr.mm"
include "wcel.mm"
include "wa.mm"
include "cz.mm"
include "eluzelz2.mm"
include "ad2antlr.mm"
include "eqid.mm"
include "cxr.mm"
include "adantr.mm"
include "wss.mm"
include "uzssd3.mm"
include "adantl.mm"
include "fssresd.mm"
include "simpr.mm"
include "cli.mm"
include "cvv.mm"
include "wb.mm"
include "fvexi.mm"
include "a1i.mm"
include "fexd.mm"
include "climres.mm"
include "syl2anr.mm"
include "mpbird.mm"
include "climxlim2lem.mm"
include "cpm.mm"
include "co.mm"
include "fuzxrpmcn.mm"
include "xlimres.mm"
include "ffnd.mm"
include "cdm.mm"
include "climcl.mm"
include "syl.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "climrescn.mm"
include "r19.29a.mm"

theorem climxlim2
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume climxlim2.m: |- ( ph -> M e. ZZ )
  assume climxlim2.z: |- Z = ( ZZ>= ` M )
  assume climxlim2.f: |- ( ph -> F : Z --> RR* )
  assume climxlim2.a: |- ( ph -> F ~~> A )


  assert |- ( ph -> F ~~>* A )

  proof
    wph
    vj
    cv
    #
    cuz
    cfv
    #
    cc
    cF
    @1
    cres
    #
    wf
    #
    cF
    cA
    clsxlim
    wbr
    #
    vj
    cZ
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @3
    wa
    #
    @4
    @2
    cA
    clsxlim
    wbr
    #
    @7
    cA
    @2
    @0
    @1
    @5
    @0
    cz
    wcel
    #
    wph
    @3
    cM
    @0
    cZ
    climxlim2.z
    eluzelz2
    #
    ad2antlr
    @1
    eqid
    @6
    @1
    cxr
    @2
    wf
    @3
    @6
    cZ
    cxr
    @1
    cF
    wph
    cZ
    cxr
    cF
    wf
    @5
    climxlim2.f
    adantr
    @5
    @1
    cZ
    wss
    wph
    cM
    @0
    cZ
    climxlim2.z
    uzssd3
    adantl
    fssresd
    adantr
    @6
    @3
    simpr
    @6
    @2
    cA
    cli
    wbr
    #
    @3
    @6
    @11
    cF
    cA
    cli
    wbr
    #
    wph
    @12
    @5
    climxlim2.a
    adantr
    @5
    @9
    cF
    cvv
    wcel
    #
    @11
    @12
    wb
    wph
    @10
    wph
    cZ
    cxr
    cvv
    cF
    climxlim2.f
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    climxlim2.z
    fvexi
    a1i
    fexd
    #
    cA
    cF
    @0
    cvv
    climres
    syl2anr
    mpbird
    adantr
    climxlim2lem
    @6
    @4
    @8
    wb
    @3
    @6
    cA
    cF
    @0
    wph
    cF
    cxr
    cc
    cpm
    co
    wcel
    @5
    wph
    cF
    cM
    cZ
    climxlim2.z
    climxlim2.f
    fuzxrpmcn
    adantr
    @5
    @9
    wph
    @10
    adantl
    xlimres
    adantr
    mpbird
    wph
    vj
    cF
    cM
    cZ
    climxlim2.m
    climxlim2.z
    wph
    cZ
    cxr
    cF
    climxlim2.f
    ffnd
    wph
    @13
    cA
    cc
    wcel
    #
    @12
    cF
    cli
    cdm
    wcel
    @14
    wph
    @12
    @15
    climxlim2.a
    cA
    cF
    climcl
    syl
    climxlim2.a
    cF
    cA
    cvv
    cc
    cli
    breldmg
    syl3anc
    climrescn
    r19.29a
end

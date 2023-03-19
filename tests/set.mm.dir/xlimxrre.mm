include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cioo.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cr.mm"
include "cres.mm"
include "wf.mm"
include "elioore.mm"
include "anim2i.mm"
include "ralimi.mm"
include "adantl.mm"
include "wb.mm"
include "wfun.mm"
include "cxr.mm"
include "ffund.mm"
include "ffvresb.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "adantrl.mm"
include "wrex.mm"
include "peano2rem.mm"
include "rexrd.mm"
include "peano2re.mm"
include "ltm1d.mm"
include "ltp1d.mm"
include "eliood.mm"
include "cle.mm"
include "cordt.mm"
include "wi.mm"
include "iooordt.mm"
include "clsxlim.mm"
include "wbr.mm"
include "nfcv.mm"
include "eqid.mm"
include "xlimbr.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "eleq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "sylancr.mm"
include "mpd.mm"
include "reximddv.mm"

theorem xlimxrre
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vu: setvar u
  let vx: setvar x
  assume xlimxrre.m: |- ( ph -> M e. ZZ )
  assume xlimxrre.z: |- Z = ( ZZ>= ` M )
  assume xlimxrre.f: |- ( ph -> F : Z --> RR* )
  assume xlimxrre.a: |- ( ph -> A e. RR )
  assume xlimxrre.c: |- ( ph -> F ~~>* A )

  disjoint A j
  disjoint F j
  disjoint M j
  disjoint Z j
  disjoint j ph
  disjoint A k
  disjoint A u
  disjoint j k
  disjoint j u
  disjoint k u
  disjoint F k
  disjoint F u
  disjoint M u
  disjoint Z k
  disjoint Z u
  disjoint k x
  assert |- ( ph -> E. j e. Z ( F |` ( ZZ>= ` j ) ) : ( ZZ>= ` j ) --> RR )

  proof
    wph
    vk
    cv
    #
    cF
    cdm
    wcel
    #
    @0
    cF
    cfv
    #
    cA
    c1
    cmin
    co
    #
    cA
    c1
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    @9
    cr
    cF
    @9
    cres
    wf
    #
    vj
    cZ
    wph
    @10
    @11
    @8
    cZ
    wcel
    wph
    @10
    wa
    @11
    @1
    @2
    cr
    wcel
    #
    wa
    #
    vk
    @9
    wral
    #
    @10
    @14
    wph
    @7
    @13
    vk
    @9
    @6
    @12
    @1
    @2
    @3
    @4
    elioore
    anim2i
    ralimi
    adantl
    wph
    @11
    @14
    wb
    #
    @10
    wph
    cF
    wfun
    @15
    wph
    cZ
    cxr
    cF
    xlimxrre.f
    ffund
    vk
    @9
    cr
    cF
    ffvresb
    syl
    adantr
    mpbird
    adantrl
    wph
    cA
    @5
    wcel
    #
    @10
    vj
    cZ
    wrex
    #
    wph
    @3
    @4
    cA
    wph
    @3
    wph
    cA
    cr
    wcel
    #
    @3
    cr
    wcel
    xlimxrre.a
    cA
    peano2rem
    syl
    rexrd
    wph
    @4
    wph
    @18
    @4
    cr
    wcel
    xlimxrre.a
    cA
    peano2re
    syl
    rexrd
    xlimxrre.a
    wph
    cA
    xlimxrre.a
    ltm1d
    wph
    cA
    xlimxrre.a
    ltp1d
    eliood
    wph
    @5
    cle
    cordt
    cfv
    #
    wcel
    cA
    vu
    cv
    #
    wcel
    #
    @1
    @2
    @20
    wcel
    #
    wa
    #
    vk
    @9
    wral
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    @19
    wral
    #
    @16
    @17
    wi
    #
    @3
    @4
    iooordt
    wph
    cA
    cxr
    wcel
    #
    @26
    wph
    cF
    cA
    clsxlim
    wbr
    @28
    @26
    wa
    xlimxrre.c
    wph
    vu
    cA
    vj
    vk
    cF
    @19
    cM
    cZ
    vk
    cF
    nfcv
    xlimxrre.m
    xlimxrre.z
    xlimxrre.f
    @19
    eqid
    xlimbr
    mpbid
    simprd
    @25
    @27
    vu
    @5
    @19
    @20
    @5
    wceq
    #
    @21
    @16
    @24
    @17
    @20
    @5
    cA
    eleq2
    @29
    @23
    @7
    vj
    vk
    cZ
    @9
    @29
    @22
    @6
    @1
    @20
    @5
    @2
    eleq2
    anbi2d
    rexralbidv
    imbi12d
    rspcva
    sylancr
    mpd
    reximddv
end

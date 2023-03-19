include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cc.mm"
include "cres.mm"
include "wf.mm"
include "wrex.mm"
include "wcel.mm"
include "cli.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wral.mm"
include "cdm.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "uztrn2.mm"
include "adantll.mm"
include "wceq.mm"
include "fndmd.mm"
include "ad2antrr.mm"
include "eleqtrrd.mm"
include "adantlr.mm"
include "rspa.mm"
include "simpld.mm"
include "adantlll.mm"
include "jca.mm"
include "ralrimia.mm"
include "wb.mm"
include "wfn.mm"
include "wfun.mm"
include "fnfun.mm"
include "ffvresb.mm"
include "3syl.mm"
include "mpbird.mm"
include "cz.mm"
include "crp.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "climdm.mm"
include "sylib.mm"
include "eqidd.mm"
include "clim.mm"
include "mpbid.mm"
include "simprd.mm"
include "1rp.mm"
include "a1i.mm"
include "rspcdva.mm"
include "rexuz3.mm"
include "syl.mm"
include "reximddv3.mm"
include "fveq2.mm"
include "reseq2d.mm"
include "feq12d.mm"
include "cbvrexv.mm"
include "sylibr.mm"

theorem climrescn
  let wph: wff ph
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  assume climrescn.m: |- ( ph -> M e. ZZ )
  assume climrescn.z: |- Z = ( ZZ>= ` M )
  assume climrescn.f: |- ( ph -> F Fn Z )
  assume climrescn.c: |- ( ph -> F e. dom ~~> )

  disjoint F j
  disjoint Z j
  disjoint F i
  disjoint i j
  disjoint F k
  disjoint F x
  disjoint i k
  disjoint i x
  disjoint k x
  disjoint M i
  disjoint Z i
  disjoint Z k
  disjoint i ph
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> E. j e. Z ( F |` ( ZZ>= ` j ) ) : ( ZZ>= ` j ) --> CC )

  proof
    wph
    vi
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
    vi
    cZ
    wrex
    vj
    cv
    #
    cuz
    cfv
    #
    cc
    cF
    @5
    cres
    #
    wf
    #
    vj
    cZ
    wrex
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @9
    cF
    cli
    cfv
    #
    cmin
    co
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    wa
    #
    vk
    @1
    wral
    #
    @3
    vi
    cZ
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @15
    wa
    #
    @3
    @8
    cF
    cdm
    #
    wcel
    #
    @10
    wa
    #
    vk
    @1
    wral
    #
    @18
    @21
    vk
    @1
    @17
    @15
    vk
    @17
    vk
    nfv
    @14
    vk
    @1
    nfra1
    nfan
    @18
    @8
    @1
    wcel
    #
    wa
    @20
    @10
    @17
    @23
    @20
    @15
    @17
    @23
    wa
    @8
    cZ
    @19
    @16
    @23
    @8
    cZ
    wcel
    wph
    cM
    @8
    @0
    cZ
    climrescn.z
    uztrn2
    adantll
    wph
    @19
    cZ
    wceq
    @16
    @23
    wph
    cZ
    cF
    climrescn.f
    fndmd
    ad2antrr
    eleqtrrd
    adantlr
    @16
    @15
    @23
    @10
    wph
    @16
    @15
    wa
    @23
    wa
    @10
    @13
    @15
    @23
    @14
    @16
    @14
    vk
    @1
    rspa
    adantll
    simpld
    adantlll
    jca
    ralrimia
    wph
    @3
    @22
    wb
    #
    @16
    @15
    wph
    cF
    cZ
    wfn
    cF
    wfun
    @24
    climrescn.f
    cZ
    cF
    fnfun
    vk
    @1
    cc
    cF
    ffvresb
    3syl
    ad2antrr
    mpbird
    wph
    @15
    vi
    cZ
    wrex
    #
    @15
    vi
    cz
    wrex
    #
    wph
    @10
    @12
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    @1
    wral
    vi
    cz
    wrex
    #
    @26
    vx
    crp
    c1
    @27
    c1
    wceq
    #
    @29
    @14
    vi
    vk
    cz
    @1
    @31
    @28
    @13
    @10
    @27
    c1
    @12
    clt
    breq2
    anbi2d
    rexralbidv
    wph
    @11
    cc
    wcel
    #
    @30
    vx
    crp
    wral
    #
    wph
    cF
    @11
    cli
    wbr
    #
    @32
    @33
    wa
    wph
    cF
    cli
    cdm
    #
    wcel
    @34
    climrescn.c
    cF
    climdm
    sylib
    wph
    vx
    @11
    @9
    vi
    vk
    cF
    @35
    climrescn.c
    wph
    @8
    cz
    wcel
    wa
    @9
    eqidd
    clim
    mpbid
    simprd
    c1
    crp
    wcel
    wph
    1rp
    a1i
    rspcdva
    wph
    cM
    cz
    wcel
    @25
    @26
    wb
    climrescn.m
    @14
    vi
    vk
    cM
    cZ
    climrescn.z
    rexuz3
    syl
    mpbird
    reximddv3
    @7
    @3
    vj
    vi
    cZ
    @4
    @0
    wceq
    #
    @5
    @1
    cc
    @6
    @2
    @36
    @5
    @1
    cF
    @4
    @0
    cuz
    fveq2
    #
    reseq2d
    @37
    feq12d
    cbvrexv
    sylibr
end

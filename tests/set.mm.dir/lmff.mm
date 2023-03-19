include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "wf.mm"
include "wrex.mm"
include "cz.mm"
include "crn.mm"
include "clm.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "cdm.mm"
include "eldm2g.mm"
include "ibi.mm"
include "syl.mm"
include "df-br.mm"
include "exbii.mm"
include "sylibr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "ctopon.mm"
include "toponmax.mm"
include "adantr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "w3a.mm"
include "lmbr.mm"
include "biimpa.mm"
include "simp3d.mm"
include "lmcl.mm"
include "sylan.mm"
include "wceq.mm"
include "eleq2.mm"
include "feq3.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "exlimddv.mm"
include "cpw.mm"
include "wfn.mm"
include "wb.mm"
include "uzf.mm"
include "ffn.mm"
include "reseq2.mm"
include "id.mm"
include "feq12d.mm"
include "rexrn.mm"
include "mp2b.mm"
include "sylib.mm"
include "rexuz3.mm"
include "wfun.mm"
include "simp1d.mm"
include "pmfun.mm"
include "ffvresb.mm"
include "3bitr4d.mm"
include "mpbird.mm"

theorem lmff
  let wph: wff ph
  let vj: setvar j
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vk: setvar k
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cS: class S
  assume lmff.1: |- Z = ( ZZ>= ` M )
  assume lmff.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume lmff.4: |- ( ph -> M e. ZZ )
  assume lmff.5: |- ( ph -> F e. dom ( ~~>t ` J ) )

  disjoint F j
  disjoint J j
  disjoint M j
  disjoint j ph
  disjoint X j
  disjoint Z j
  disjoint j k
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J k
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint M k
  disjoint P j
  disjoint P k
  disjoint P u
  disjoint S k
  disjoint S u
  disjoint k ph
  disjoint ph u
  disjoint ph y
  disjoint X k
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint Z k
  disjoint Z u
  disjoint Z x
  assert |- ( ph -> E. j e. Z ( F |` ( ZZ>= ` j ) ) : ( ZZ>= ` j ) --> X )

  proof
    wph
    vj
    cv
    #
    cuz
    cfv
    #
    cX
    cF
    @1
    cres
    #
    wf
    #
    vj
    cZ
    wrex
    #
    @3
    vj
    cz
    wrex
    #
    wph
    vx
    cv
    #
    cX
    cF
    @6
    cres
    #
    wf
    #
    vx
    cuz
    crn
    #
    wrex
    #
    @5
    wph
    cF
    vy
    cv
    #
    cJ
    clm
    cfv
    #
    wbr
    #
    @10
    vy
    wph
    cF
    @11
    cop
    @12
    wcel
    #
    vy
    wex
    #
    @13
    vy
    wex
    wph
    cF
    @12
    cdm
    #
    wcel
    #
    @15
    lmff.5
    @17
    @15
    vy
    cF
    @12
    @16
    eldm2g
    ibi
    syl
    @13
    @14
    vy
    cF
    @11
    @12
    df-br
    exbii
    sylibr
    #
    wph
    @13
    wa
    #
    cX
    cJ
    wcel
    #
    @11
    @0
    wcel
    #
    @6
    @0
    @7
    wf
    #
    vx
    @9
    wrex
    #
    wi
    #
    vj
    cJ
    wral
    #
    @11
    cX
    wcel
    #
    @10
    wph
    @20
    @13
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @20
    lmff.3
    cX
    cJ
    toponmax
    syl
    adantr
    @19
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    @26
    @25
    wph
    @13
    @28
    @26
    @25
    w3a
    wph
    vx
    vj
    @11
    cF
    cJ
    cX
    lmff.3
    lmbr
    biimpa
    #
    simp3d
    wph
    @27
    @13
    @26
    lmff.3
    @11
    cF
    cJ
    cX
    lmcl
    sylan
    @24
    @26
    @10
    wi
    vj
    cX
    cJ
    @0
    cX
    wceq
    #
    @21
    @26
    @23
    @10
    @0
    cX
    @11
    eleq2
    @30
    @22
    @8
    vx
    @9
    @0
    cX
    @6
    @7
    feq3
    rexbidv
    imbi12d
    rspcv
    syl3c
    exlimddv
    cz
    cz
    cpw
    #
    cuz
    wf
    cuz
    cz
    wfn
    @10
    @5
    wb
    uzf
    cz
    @31
    cuz
    ffn
    @8
    @3
    vx
    vj
    cz
    cuz
    @6
    @1
    wceq
    #
    @6
    @1
    cX
    @7
    @2
    @6
    @1
    cF
    reseq2
    @32
    id
    feq12d
    rexrn
    mp2b
    sylib
    wph
    @6
    cF
    cdm
    wcel
    @6
    cF
    cfv
    cX
    wcel
    wa
    #
    vx
    @1
    wral
    #
    vj
    cZ
    wrex
    #
    @34
    vj
    cz
    wrex
    #
    @4
    @5
    wph
    cM
    cz
    wcel
    @35
    @36
    wb
    lmff.4
    @33
    vj
    vx
    cM
    cZ
    lmff.1
    rexuz3
    syl
    wph
    @3
    @34
    vj
    cZ
    wph
    cF
    wfun
    #
    @3
    @34
    wb
    wph
    @28
    @37
    wph
    @13
    @28
    vy
    @18
    @19
    @28
    @26
    @25
    @29
    simp1d
    exlimddv
    cX
    cc
    cF
    pmfun
    syl
    vx
    @1
    cX
    cF
    ffvresb
    syl
    #
    rexbidv
    wph
    @3
    @34
    vj
    cz
    @38
    rexbidv
    3bitr4d
    mpbird
end

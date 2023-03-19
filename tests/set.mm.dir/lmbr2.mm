include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cdm.mm"
include "wa.mm"
include "lmbr.mm"
include "cz.mm"
include "cpw.mm"
include "wfn.mm"
include "wb.mm"
include "uzf.mm"
include "ffn.mm"
include "wceq.mm"
include "reseq2.mm"
include "id.mm"
include "feq12d.mm"
include "rexrn.mm"
include "mp2b.mm"
include "wfun.mm"
include "pmfun.mm"
include "ad2antrl.mm"
include "ffvresb.mm"
include "syl.mm"
include "rexbidv.mm"
include "adantr.mm"
include "rexuz3.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem lmbr2
  let wph: wff ph
  let vu: setvar u
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lmbr.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume lmbr2.4: |- Z = ( ZZ>= ` M )
  assume lmbr2.5: |- ( ph -> M e. ZZ )

  disjoint j k
  disjoint j u
  disjoint F j
  disjoint k u
  disjoint F k
  disjoint F u
  disjoint J j
  disjoint J k
  disjoint J u
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint Z j
  disjoint Z k
  disjoint Z u
  disjoint M j
  disjoint P j
  disjoint P k
  disjoint P u
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint f j
  disjoint f k
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J f
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint P f
  disjoint P x
  disjoint P z
  disjoint X f
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F e. ( X ^pm CC ) /\ P e. X /\ A. u e. J ( P e. u -> E. j e. Z A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. u ) ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    vu
    cv
    #
    wcel
    #
    vz
    cv
    #
    @2
    cF
    @4
    cres
    #
    wf
    #
    vz
    cuz
    crn
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    #
    @0
    @1
    @3
    vk
    cv
    #
    cF
    cdm
    wcel
    @11
    cF
    cfv
    @2
    wcel
    wa
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    w3a
    #
    wph
    vz
    vu
    cP
    cF
    cJ
    cX
    lmbr.2
    lmbr
    wph
    @0
    @1
    wa
    #
    @9
    wa
    @19
    @17
    wa
    @10
    @18
    wph
    @19
    @9
    @17
    wph
    @19
    wa
    #
    @8
    @16
    vu
    cJ
    @20
    @7
    @15
    @3
    @7
    @13
    @2
    cF
    @13
    cres
    #
    wf
    #
    vj
    cz
    wrex
    #
    @20
    @15
    cz
    cz
    cpw
    #
    cuz
    wf
    cuz
    cz
    wfn
    @7
    @23
    wb
    uzf
    cz
    @24
    cuz
    ffn
    @6
    @22
    vz
    vj
    cz
    cuz
    @4
    @13
    wceq
    #
    @4
    @13
    @2
    @5
    @21
    @4
    @13
    cF
    reseq2
    @25
    id
    feq12d
    rexrn
    mp2b
    @20
    @23
    @14
    vj
    cz
    wrex
    #
    @15
    @20
    @22
    @14
    vj
    cz
    @20
    cF
    wfun
    #
    @22
    @14
    wb
    @0
    @27
    wph
    @1
    cX
    cc
    cF
    pmfun
    ad2antrl
    vk
    @13
    @2
    cF
    ffvresb
    syl
    rexbidv
    @20
    cM
    cz
    wcel
    #
    @15
    @26
    wb
    wph
    @28
    @19
    lmbr2.5
    adantr
    @12
    vj
    vk
    cM
    cZ
    lmbr2.4
    rexuz3
    syl
    bitr4d
    syl5bb
    imbi2d
    ralbidv
    pm5.32da
    @0
    @1
    @9
    df-3an
    @0
    @1
    @17
    df-3an
    3bitr4g
    bitrd
end

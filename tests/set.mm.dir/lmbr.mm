include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cres.mm"
include "wf.mm"
include "cuz.mm"
include "crn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "copab.mm"
include "ctopon.mm"
include "wceq.mm"
include "lmfval.mm"
include "syl.mm"
include "breqd.mm"
include "wa.mm"
include "reseq1.mm"
include "feq1d.mm"
include "rexbidv.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "sylan9bb.mm"
include "df-3an.mm"
include "opabbii.mm"
include "brab2a.mm"
include "bitr4i.mm"
include "syl6bb.mm"

theorem lmbr
  let wph: wff ph
  let vy: setvar y
  let vu: setvar u
  let cP: class P
  let cF: class F
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z
  let cZ: class Z
  let cM: class M
  assume lmbr.2: |- ( ph -> J e. ( TopOn ` X ) )

  disjoint u y
  disjoint F u
  disjoint F y
  disjoint J u
  disjoint J y
  disjoint ph u
  disjoint P u
  disjoint X u
  disjoint X y
  disjoint f j
  disjoint f k
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint j k
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint u x
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F z
  disjoint J f
  disjoint J j
  disjoint J k
  disjoint J x
  disjoint J z
  disjoint j ph
  disjoint k ph
  disjoint Z j
  disjoint Z k
  disjoint Z u
  disjoint M j
  disjoint P f
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint P z
  disjoint X f
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint X z
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F e. ( X ^pm CC ) /\ P e. X /\ A. u e. J ( P e. u -> E. y e. ran ZZ>= ( F |` y ) : y --> u ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    #
    wbr
    cF
    cP
    vf
    cv
    #
    cX
    cc
    cpm
    co
    #
    wcel
    #
    vx
    cv
    #
    cX
    wcel
    #
    @4
    vu
    cv
    #
    wcel
    #
    vy
    cv
    #
    @6
    @1
    @8
    cres
    #
    wf
    #
    vy
    cuz
    crn
    #
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
    vf
    vx
    copab
    #
    wbr
    #
    cF
    @2
    wcel
    #
    cP
    cX
    wcel
    #
    cP
    @6
    wcel
    #
    @8
    @6
    cF
    @8
    cres
    #
    wf
    #
    vy
    @11
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
    @0
    @16
    cF
    cP
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @0
    @16
    wceq
    lmbr.2
    vx
    vy
    vu
    vf
    cJ
    cX
    lmfval
    syl
    breqd
    @17
    @18
    @19
    wa
    @25
    wa
    @26
    @14
    @25
    vf
    vx
    cF
    cP
    @2
    cX
    @16
    @1
    cF
    wceq
    #
    @14
    @7
    @23
    wi
    #
    vu
    cJ
    wral
    @4
    cP
    wceq
    #
    @25
    @27
    @13
    @28
    vu
    cJ
    @27
    @12
    @23
    @7
    @27
    @10
    @22
    vy
    @11
    @27
    @8
    @6
    @9
    @21
    @1
    cF
    @8
    reseq1
    feq1d
    rexbidv
    imbi2d
    ralbidv
    @29
    @28
    @24
    vu
    cJ
    @29
    @7
    @20
    @23
    @4
    cP
    @6
    eleq1
    imbi1d
    ralbidv
    sylan9bb
    @15
    @3
    @5
    wa
    @14
    wa
    vf
    vx
    @3
    @5
    @14
    df-3an
    opabbii
    brab2a
    @18
    @19
    @25
    df-3an
    bitr4i
    syl6bb
end

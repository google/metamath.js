include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "lmbr2.mm"
include "3anass.mm"
include "wb.mm"
include "uztrn2.mm"
include "eleq1d.mm"
include "wf.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "cvv.mm"
include "wss.mm"
include "ctopon.mm"
include "toponmax.mm"
include "cnex.mm"
include "jctir.mm"
include "cz.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "eqsstri.mm"
include "elpm2r.mm"
include "syl2anc.mm"
include "bitr2d.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem lmbrf
  let wph: wff ph
  let vu: setvar u
  let cA: class A
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
  assume lmbrf.6: |- ( ph -> F : Z --> X )
  assume lmbrf.7: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )

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
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( P e. X /\ A. u e. J ( P e. u -> E. j e. Z A. k e. ( ZZ>= ` j ) A e. u ) ) ) )

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
    vk
    cv
    #
    cF
    cdm
    #
    wcel
    #
    @4
    cF
    cfv
    #
    @2
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
    @1
    @3
    cA
    @2
    wcel
    #
    vk
    @11
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
    wa
    #
    wph
    vu
    cP
    vj
    vk
    cF
    cJ
    cM
    cX
    cZ
    lmbr.2
    lmbr2.4
    lmbr2.5
    lmbr2
    @16
    @0
    @1
    @15
    wa
    #
    wa
    #
    wph
    @22
    @0
    @1
    @15
    3anass
    wph
    @22
    @23
    @24
    wph
    @21
    @15
    @1
    wph
    @20
    @14
    vu
    cJ
    wph
    @19
    @13
    @3
    wph
    @18
    @12
    vj
    cZ
    wph
    @10
    cZ
    wcel
    #
    wa
    @17
    @9
    vk
    @11
    wph
    @25
    @4
    @11
    wcel
    #
    @17
    @9
    wb
    #
    @25
    @26
    wa
    wph
    @4
    cZ
    wcel
    #
    @27
    cM
    @4
    @10
    cZ
    lmbr2.4
    uztrn2
    wph
    @28
    wa
    #
    @8
    @17
    @9
    @29
    @7
    cA
    @2
    lmbrf.7
    eleq1d
    @29
    @6
    @8
    wph
    @6
    @28
    wph
    @5
    cZ
    @4
    wph
    cZ
    cX
    cF
    wf
    #
    @5
    cZ
    wceq
    lmbrf.6
    cZ
    cX
    cF
    fdm
    syl
    eleq2d
    biimpar
    biantrurd
    bitr3d
    sylan2
    anassrs
    ralbidva
    rexbidva
    imbi2d
    ralbidv
    anbi2d
    wph
    @0
    @23
    wph
    cX
    cJ
    wcel
    #
    cc
    cvv
    wcel
    #
    wa
    @30
    cZ
    cc
    wss
    #
    wa
    @0
    wph
    @31
    @32
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @31
    lmbr.2
    cX
    cJ
    toponmax
    syl
    cnex
    jctir
    wph
    @30
    @33
    lmbrf.6
    cZ
    cM
    cuz
    cfv
    #
    cc
    lmbr2.4
    @34
    cz
    cc
    cM
    uzssz
    zsscn
    sstri
    eqsstri
    jctir
    cX
    cc
    cZ
    cF
    cJ
    cvv
    elpm2r
    syl2anc
    biantrurd
    bitr2d
    syl5bb
    bitrd
end

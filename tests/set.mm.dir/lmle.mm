include "cv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "wf.mm"
include "cxmt.mm"
include "ctopon.mm"
include "mopntopon.mm"
include "syl.mm"
include "clm.mm"
include "wrel.mm"
include "cdm.mm"
include "lmrel.mm"
include "releldm.mm"
include "sylancr.mm"
include "lmff.mm"
include "wa.mm"
include "eqid.mm"
include "adantr.mm"
include "cz.mm"
include "simprl.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "simprr.mm"
include "ffvelrnda.mm"
include "eqeltrrd.mm"
include "uztrn2.mm"
include "sylan.mm"
include "adantlr.mm"
include "syldan.mm"
include "oveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ccld.mm"
include "cxr.mm"
include "blcld.mm"
include "syl3anc.mm"
include "lmcld.mm"
include "rexlimddv.mm"
include "simprbi.mm"

theorem lmle
  let wph: wff ph
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vx: setvar x
  assume lmle.1: |- Z = ( ZZ>= ` M )
  assume lmle.3: |- J = ( MetOpen ` D )
  assume lmle.4: |- ( ph -> D e. ( *Met ` X ) )
  assume lmle.6: |- ( ph -> M e. ZZ )
  assume lmle.7: |- ( ph -> F ( ~~>t ` J ) P )
  assume lmle.8: |- ( ph -> Q e. X )
  assume lmle.9: |- ( ph -> R e. RR* )
  assume lmle.10: |- ( ( ph /\ k e. Z ) -> ( Q D ( F ` k ) ) <_ R )

  disjoint D k
  disjoint J k
  disjoint k ph
  disjoint Z k
  disjoint F k
  disjoint P k
  disjoint Q k
  disjoint R k
  disjoint X k
  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D x
  disjoint J j
  disjoint M j
  disjoint j ph
  disjoint Z j
  disjoint F j
  disjoint F x
  disjoint P j
  disjoint P x
  disjoint Q j
  disjoint Q x
  disjoint R j
  disjoint R x
  disjoint X j
  disjoint X x
  assert |- ( ph -> ( Q D P ) <_ R )

  proof
    wph
    cP
    cQ
    vx
    cv
    #
    cD
    co
    #
    cR
    cle
    wbr
    #
    vx
    cX
    crab
    #
    wcel
    #
    cQ
    cP
    cD
    co
    #
    cR
    cle
    wbr
    #
    wph
    vj
    cv
    #
    cuz
    cfv
    #
    cX
    cF
    @8
    cres
    #
    wf
    #
    @4
    vj
    cZ
    wph
    vj
    cF
    cJ
    cM
    cX
    cZ
    lmle.1
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    lmle.4
    cD
    cJ
    cX
    lmle.3
    mopntopon
    syl
    #
    lmle.6
    wph
    cJ
    clm
    cfv
    #
    wrel
    cF
    cP
    @14
    wbr
    #
    cF
    @14
    cdm
    wcel
    cJ
    lmrel
    lmle.7
    cF
    cP
    @14
    releldm
    sylancr
    lmff
    wph
    @7
    cZ
    wcel
    #
    @10
    wa
    #
    wa
    #
    cP
    @3
    vk
    cF
    cJ
    @7
    cX
    @8
    @8
    eqid
    wph
    @12
    @17
    @13
    adantr
    @18
    @7
    cM
    cuz
    cfv
    #
    wcel
    @7
    cz
    wcel
    @18
    @7
    cZ
    @19
    wph
    @16
    @10
    simprl
    #
    lmle.1
    syl6eleq
    cM
    @7
    eluzelz
    syl
    wph
    @15
    @17
    lmle.7
    adantr
    @18
    vk
    cv
    #
    @8
    wcel
    #
    wa
    #
    @21
    cF
    cfv
    #
    cX
    wcel
    cQ
    @24
    cD
    co
    #
    cR
    cle
    wbr
    #
    @24
    @3
    wcel
    @23
    @21
    @9
    cfv
    #
    @24
    cX
    @22
    @27
    @24
    wceq
    @18
    @21
    @8
    cF
    fvres
    adantl
    @18
    @8
    cX
    @21
    @9
    wph
    @16
    @10
    simprr
    ffvelrnda
    eqeltrrd
    @18
    @22
    @21
    cZ
    wcel
    #
    @26
    @18
    @16
    @22
    @28
    @20
    cM
    @21
    @7
    cZ
    lmle.1
    uztrn2
    sylan
    wph
    @28
    @26
    @17
    lmle.10
    adantlr
    syldan
    @2
    @26
    vx
    @24
    cX
    @0
    @24
    wceq
    @1
    @25
    cR
    cle
    @0
    @24
    cQ
    cD
    oveq2
    breq1d
    elrab
    sylanbrc
    wph
    @3
    cJ
    ccld
    cfv
    wcel
    #
    @17
    wph
    @11
    cQ
    cX
    wcel
    cR
    cxr
    wcel
    @29
    lmle.4
    lmle.8
    lmle.9
    vx
    cD
    cQ
    cR
    @3
    cJ
    cX
    lmle.3
    @3
    eqid
    blcld
    syl3anc
    adantr
    lmcld
    rexlimddv
    @4
    cP
    cX
    wcel
    @6
    @2
    @6
    vx
    cP
    cX
    @0
    cP
    wceq
    @1
    @5
    cR
    cle
    @0
    cP
    cQ
    cD
    oveq2
    breq1d
    elrab
    simprbi
    syl
end

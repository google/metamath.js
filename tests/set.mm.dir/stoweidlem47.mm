include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "cmin.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "csn.mm"
include "cxp.mm"
include "fveq1i.mm"
include "cr.mm"
include "wceq.mm"
include "renegcld.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "fcnre.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "cc.mm"
include "adantr.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "mpteq2da.mm"
include "ccn.mm"
include "nfcv.mm"
include "nfneg.mm"
include "nfsn.mm"
include "nfxp.mm"
include "nfcxfr.mm"
include "ctop.mm"
include "cuni.mm"
include "ctopon.mm"
include "a1i.mm"
include "istopon.mm"
include "sylanbrc.mm"
include "syl6eleq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "cnconst2.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "refsum2cn.mm"
include "syl6eleqr.mm"
include "eqeltrrd.mm"

theorem stoweidlem47
  let wph: wff ph
  let vt: setvar t
  let cC: class C
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem47.1: |- F/_ t F
  assume stoweidlem47.2: |- F/_ t S
  assume stoweidlem47.3: |- F/ t ph
  assume stoweidlem47.4: |- T = U. J
  assume stoweidlem47.5: |- G = ( T X. { -u S } )
  assume stoweidlem47.6: |- K = ( topGen ` ran (,) )
  assume stoweidlem47.7: |- ( ph -> J e. Top )
  assume stoweidlem47.8: |- C = ( J Cn K )
  assume stoweidlem47.9: |- ( ph -> F e. C )
  assume stoweidlem47.10: |- ( ph -> S e. RR )

  disjoint J t
  disjoint K t
  disjoint T t
  disjoint k x
  assert |- ( ph -> ( t e. T |-> ( ( F ` t ) - S ) ) e. C )

  proof
    wph
    vt
    cT
    vt
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    vt
    cT
    @1
    cS
    cmin
    co
    #
    cmpt
    cC
    wph
    vt
    cT
    @3
    @5
    stoweidlem47.3
    wph
    @0
    cT
    wcel
    #
    wa
    #
    @3
    @1
    cS
    cneg
    #
    caddc
    co
    @5
    @7
    @2
    @8
    @1
    caddc
    @7
    @2
    @0
    cT
    @8
    csn
    #
    cxp
    #
    cfv
    #
    @8
    @0
    cG
    @10
    stoweidlem47.5
    fveq1i
    wph
    @8
    cr
    wcel
    #
    @6
    @11
    @8
    wceq
    wph
    cS
    stoweidlem47.10
    renegcld
    #
    cT
    @8
    @0
    cr
    fvconst2g
    sylan
    syl5eq
    oveq2d
    @7
    @1
    cS
    @7
    @1
    wph
    cT
    cr
    @0
    cF
    wph
    cC
    cT
    cF
    cJ
    cK
    stoweidlem47.6
    stoweidlem47.4
    stoweidlem47.8
    stoweidlem47.9
    fcnre
    ffvelrnda
    recnd
    wph
    cS
    cc
    wcel
    @6
    wph
    cS
    stoweidlem47.10
    recnd
    adantr
    negsubd
    eqtrd
    mpteq2da
    wph
    @4
    cJ
    cK
    ccn
    co
    #
    cC
    wph
    vt
    cF
    cG
    cJ
    cK
    cT
    stoweidlem47.1
    vt
    cG
    @10
    stoweidlem47.5
    vt
    cT
    @9
    vt
    cT
    nfcv
    vt
    @8
    vt
    cS
    stoweidlem47.2
    nfneg
    nfsn
    nfxp
    nfcxfr
    stoweidlem47.3
    stoweidlem47.6
    wph
    cJ
    ctop
    wcel
    cT
    cJ
    cuni
    wceq
    #
    cJ
    cT
    ctopon
    cfv
    wcel
    #
    stoweidlem47.7
    @15
    wph
    stoweidlem47.4
    a1i
    cT
    cJ
    istopon
    sylanbrc
    #
    wph
    cF
    cC
    @14
    stoweidlem47.9
    stoweidlem47.8
    syl6eleq
    wph
    cG
    @10
    @14
    stoweidlem47.5
    wph
    @16
    cK
    cr
    ctopon
    cfv
    #
    wcel
    #
    @12
    @10
    @14
    wcel
    @17
    @19
    wph
    cK
    cioo
    crn
    ctg
    cfv
    @18
    stoweidlem47.6
    retopon
    eqeltri
    a1i
    @13
    @8
    cJ
    cK
    cT
    cr
    cnconst2
    syl3anc
    syl5eqel
    refsum2cn
    stoweidlem47.8
    syl6eleqr
    eqeltrrd
end

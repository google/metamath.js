include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "cc0.mm"
include "caddc.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "adantr.mm"
include "wa.mm"
include "0cnd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "dvmptc.mm"
include "cdm.mm"
include "dmeqd.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqtrd.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "eqid.mm"
include "cnt.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "cr.mm"
include "cpr.mm"
include "recnprss.mm"
include "resttopon.mm"
include "sylancr.mm"
include "topontop.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "ntrss2.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "dvbssntr.mm"
include "eqsstr3d.mm"
include "eqssd.mm"
include "dvmptres2.mm"
include "dvmptmul.mm"
include "mul02d.mm"
include "oveq1d.mm"
include "dvmptcl.mm"
include "mulcld.mm"
include "addid2d.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"

theorem dvmptcmul
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cV: class V
  let cX: class X
  let cW: class W
  let cY: class Y
  let cZ: class Z
  assume dvmptadd.s: |- ( ph -> S e. { RR , CC } )
  assume dvmptadd.a: |- ( ( ph /\ x e. X ) -> A e. CC )
  assume dvmptadd.b: |- ( ( ph /\ x e. X ) -> B e. V )
  assume dvmptadd.da: |- ( ph -> ( S _D ( x e. X |-> A ) ) = ( x e. X |-> B ) )
  assume dvmptcmul.c: |- ( ph -> C e. CC )

  disjoint C x
  disjoint ph x
  disjoint S x
  disjoint V x
  disjoint X x
  disjoint W x
  disjoint Y x
  disjoint Z x
  assert |- ( ph -> ( S _D ( x e. X |-> ( C x. A ) ) ) = ( x e. X |-> ( C x. B ) ) )

  proof
    wph
    cS
    vx
    cX
    cC
    cA
    cmul
    co
    cmpt
    cdv
    co
    vx
    cX
    cc0
    cA
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    vx
    cX
    cC
    cB
    cmul
    co
    #
    cmpt
    wph
    vx
    cC
    cc0
    cA
    cB
    cS
    cc
    cV
    cX
    dvmptadd.s
    wph
    cC
    cc
    wcel
    #
    vx
    cv
    #
    cX
    wcel
    #
    dvmptcmul.c
    adantr
    #
    wph
    @6
    wa
    #
    0cnd
    wph
    vx
    cC
    cc0
    cS
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @9
    cc
    cS
    cX
    cX
    dvmptadd.s
    wph
    @4
    @5
    cS
    wcel
    #
    dvmptcmul.c
    adantr
    wph
    @11
    wa
    0cnd
    wph
    vx
    cC
    cS
    dvmptadd.s
    dvmptcmul.c
    dvmptc
    wph
    cX
    cS
    vx
    cX
    cA
    cmpt
    #
    cdv
    co
    #
    cdm
    #
    cS
    wph
    @14
    vx
    cX
    cB
    cmpt
    #
    cdm
    #
    cX
    wph
    @13
    @15
    dvmptadd.da
    dmeqd
    wph
    cB
    cV
    wcel
    #
    vx
    cX
    wral
    @16
    cX
    wceq
    wph
    @17
    vx
    cX
    dvmptadd.b
    ralrimiva
    vx
    cX
    cB
    cV
    dmmptg
    syl
    eqtrd
    #
    cS
    @12
    dvbsss
    syl6eqssr
    #
    @10
    eqid
    #
    @9
    eqid
    #
    wph
    cX
    @10
    cnt
    cfv
    cfv
    #
    cX
    wph
    @10
    ctop
    wcel
    #
    cX
    @10
    cuni
    #
    wss
    @22
    cX
    wss
    wph
    @10
    cS
    ctopon
    cfv
    wcel
    #
    @23
    wph
    @9
    cc
    ctopon
    cfv
    wcel
    cS
    cc
    wss
    #
    @25
    @9
    @21
    cnfldtopon
    wph
    cS
    cr
    cc
    cpr
    wcel
    @26
    dvmptadd.s
    cS
    recnprss
    syl
    #
    cS
    @9
    cc
    resttopon
    sylancr
    #
    cS
    @10
    topontop
    syl
    wph
    cX
    cS
    @24
    @19
    wph
    @25
    cS
    @24
    wceq
    @28
    cS
    @10
    toponuni
    syl
    sseqtrd
    cX
    @10
    @24
    @24
    eqid
    ntrss2
    syl2anc
    wph
    cX
    @14
    @22
    @18
    wph
    cX
    cS
    @12
    @10
    @9
    @27
    wph
    vx
    cX
    cA
    cc
    @12
    dvmptadd.a
    @12
    eqid
    fmptd
    @19
    @20
    @21
    dvbssntr
    eqsstr3d
    eqssd
    dvmptres2
    dvmptadd.a
    dvmptadd.b
    dvmptadd.da
    dvmptmul
    wph
    vx
    cX
    @2
    @3
    @8
    @2
    cc0
    @1
    caddc
    co
    @1
    @3
    @8
    @0
    cc0
    @1
    caddc
    @8
    cA
    dvmptadd.a
    mul02d
    oveq1d
    @8
    @1
    @8
    cB
    cC
    wph
    vx
    cA
    cB
    cS
    cV
    cX
    dvmptadd.s
    dvmptadd.a
    dvmptadd.b
    dvmptadd.da
    dvmptcl
    #
    @7
    mulcld
    addid2d
    @8
    cB
    cC
    @29
    @7
    mulcomd
    3eqtrd
    mpteq2dva
    eqtrd
end

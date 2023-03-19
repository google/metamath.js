include "crest.mm"
include "co.mm"
include "ccn.mm"
include "cres.mm"
include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "ccvm.mm"
include "cvmtop1.mm"
include "syl.mm"
include "cnrest2r.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wfn.mm"
include "crn.mm"
include "ffn.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "df-ima.mm"
include "syl5eqssr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "wa.mm"
include "ccom.mm"
include "wf1.mm"
include "wceq.mm"
include "wf1o.mm"
include "cfv.mm"
include "simpld.mm"
include "cvmsf1o.mm"
include "syl3anc.mm"
include "adantr.mm"
include "f1of1.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "cvmsss.mm"
include "sseldd.mm"
include "toponss.mm"
include "resttopon.mm"
include "sylan.mm"
include "f1imacnv.mm"
include "imaeq2d.mm"
include "imaco.mm"
include "cnvco.mm"
include "cores.mm"
include "resco.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "syl5eqr.mm"
include "imaeq1d.mm"
include "eqtr3d.mm"
include "cnrest.mm"
include "resima2.mm"
include "wb.mm"
include "restopn2.mm"
include "simprbda.mm"
include "cvmopn.mm"
include "eqeltrd.mm"
include "cnima.mm"
include "ralrimiva.mm"
include "iscn.mm"
include "mpbir2and.mm"

theorem cvmlift2lem9a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cF: class F
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x
  assume cvmlift2lem9a.b: |- B = U. C
  assume cvmlift2lem9a.y: |- Y = U. K
  assume cvmlift2lem9a.s: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\ ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmlift2lem9a.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift2lem9a.h: |- ( ph -> H : Y --> B )
  assume cvmlift2lem9a.g: |- ( ph -> ( F o. H ) e. ( K Cn J ) )
  assume cvmlift2lem9a.k: |- ( ph -> K e. Top )
  assume cvmlift2lem9a.1: |- ( ph -> X e. Y )
  assume cvmlift2lem9a.2: |- ( ph -> T e. ( S ` A ) )
  assume cvmlift2lem9a.3: |- ( ph -> ( W e. T /\ ( H ` X ) e. W ) )
  assume cvmlift2lem9a.4: |- ( ph -> M C_ Y )
  assume cvmlift2lem9a.6: |- ( ph -> ( H " M ) C_ W )

  disjoint c d
  disjoint c k
  disjoint c s
  disjoint A c
  disjoint d k
  disjoint d s
  disjoint A d
  disjoint k s
  disjoint A k
  disjoint A s
  disjoint F c
  disjoint F d
  disjoint F k
  disjoint F s
  disjoint J c
  disjoint J d
  disjoint J k
  disjoint J s
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint C c
  disjoint C d
  disjoint C k
  disjoint C s
  disjoint W c
  disjoint W d
  disjoint H x
  disjoint c x
  disjoint d x
  disjoint k x
  disjoint s x
  disjoint C x
  disjoint K x
  disjoint M x
  disjoint ph x
  disjoint W x
  assert |- ( ph -> ( H |` M ) e. ( ( K |`t M ) Cn C ) )

  proof
    wph
    cK
    cM
    crest
    co
    #
    cC
    cW
    crest
    co
    #
    ccn
    co
    #
    @0
    cC
    ccn
    co
    #
    cH
    cM
    cres
    #
    wph
    cC
    ctop
    wcel
    #
    @2
    @3
    wss
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @5
    cvmlift2lem9a.f
    cC
    cF
    cJ
    cvmtop1
    syl
    #
    cW
    @0
    cC
    cnrest2r
    syl
    wph
    @4
    @2
    wcel
    #
    cM
    cW
    @4
    wf
    #
    @4
    ccnv
    #
    vx
    cv
    #
    cima
    #
    @0
    wcel
    #
    vx
    @1
    wral
    #
    wph
    @4
    cM
    wfn
    #
    @4
    crn
    #
    cW
    wss
    #
    @9
    wph
    cH
    cY
    wfn
    #
    cM
    cY
    wss
    #
    @15
    wph
    cY
    cB
    cH
    wf
    @18
    cvmlift2lem9a.h
    cY
    cB
    cH
    ffn
    syl
    cvmlift2lem9a.4
    cY
    cM
    cH
    fnssres
    syl2anc
    wph
    @16
    cH
    cM
    cima
    cW
    cH
    cM
    df-ima
    cvmlift2lem9a.6
    syl5eqssr
    #
    cM
    cW
    @4
    df-f
    sylanbrc
    wph
    @13
    vx
    @1
    wph
    @11
    @1
    wcel
    #
    wa
    #
    @12
    cF
    cH
    ccom
    #
    cM
    cres
    #
    ccnv
    #
    cF
    cW
    cres
    #
    @11
    cima
    #
    cima
    #
    @0
    @22
    @10
    @26
    ccnv
    #
    @27
    cima
    #
    cima
    #
    @12
    @28
    @22
    @30
    @11
    @10
    @22
    cW
    cA
    @26
    wf1
    #
    @11
    cW
    wss
    #
    @30
    @11
    wceq
    @22
    cW
    cA
    @26
    wf1o
    #
    @32
    wph
    @34
    @21
    wph
    @6
    cT
    cA
    cS
    cfv
    wcel
    #
    cW
    cT
    wcel
    #
    @34
    cvmlift2lem9a.f
    cvmlift2lem9a.2
    wph
    @36
    cX
    cH
    cfv
    cW
    wcel
    cvmlift2lem9a.3
    simpld
    #
    vd
    vc
    cW
    cC
    cS
    cT
    cA
    vk
    cF
    cJ
    vs
    cvmlift2lem9a.s
    cvmsf1o
    syl3anc
    adantr
    cW
    cA
    @26
    f1of1
    syl
    wph
    @1
    cW
    ctopon
    cfv
    wcel
    #
    @21
    @33
    wph
    cC
    cB
    ctopon
    cfv
    wcel
    #
    cW
    cB
    wss
    #
    @38
    wph
    @5
    @39
    @7
    cC
    cB
    cvmlift2lem9a.b
    toptopon
    sylib
    #
    wph
    @39
    cW
    cC
    wcel
    #
    @40
    @41
    wph
    cT
    cC
    cW
    wph
    @35
    cT
    cC
    wss
    cvmlift2lem9a.2
    vd
    vc
    cC
    cS
    cT
    cA
    vk
    cF
    cJ
    vs
    cvmlift2lem9a.s
    cvmsss
    syl
    @37
    sseldd
    #
    cW
    cC
    cB
    toponss
    syl2anc
    cW
    cC
    cB
    resttopon
    syl2anc
    #
    @11
    @1
    cW
    toponss
    sylan
    #
    cW
    cA
    @11
    @26
    f1imacnv
    syl2anc
    imaeq2d
    @22
    @31
    @10
    @29
    ccom
    #
    @27
    cima
    @28
    @10
    @29
    @27
    imaco
    @22
    @46
    @25
    @27
    @22
    @46
    @26
    @4
    ccom
    #
    ccnv
    @25
    @26
    @4
    cnvco
    @22
    @47
    @24
    wph
    @47
    @24
    wceq
    @21
    wph
    @47
    cF
    @4
    ccom
    #
    @24
    wph
    @17
    @47
    @48
    wceq
    @20
    cF
    @4
    cW
    cores
    syl
    cF
    cH
    cM
    resco
    syl6eqr
    adantr
    cnveqd
    syl5eqr
    imaeq1d
    syl5eqr
    eqtr3d
    @22
    @24
    @0
    cJ
    ccn
    co
    wcel
    #
    @27
    cJ
    wcel
    @28
    @0
    wcel
    wph
    @49
    @21
    wph
    @23
    cK
    cJ
    ccn
    co
    wcel
    @19
    @49
    cvmlift2lem9a.g
    cvmlift2lem9a.4
    cM
    @23
    cK
    cJ
    cY
    cvmlift2lem9a.y
    cnrest
    syl2anc
    adantr
    @22
    @27
    cF
    @11
    cima
    #
    cJ
    @22
    @33
    @27
    @50
    wceq
    @45
    cF
    @11
    cW
    resima2
    syl
    @22
    @6
    @11
    cC
    wcel
    #
    @50
    cJ
    wcel
    wph
    @6
    @21
    cvmlift2lem9a.f
    adantr
    wph
    @21
    @51
    @33
    wph
    @5
    @42
    @21
    @51
    @33
    wa
    wb
    @7
    @43
    cW
    @11
    cC
    restopn2
    syl2anc
    simprbda
    @11
    cC
    cF
    cJ
    cvmopn
    syl2anc
    eqeltrd
    @27
    @24
    @0
    cJ
    cnima
    syl2anc
    eqeltrd
    ralrimiva
    wph
    @0
    cM
    ctopon
    cfv
    wcel
    #
    @38
    @8
    @9
    @14
    wa
    wb
    wph
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @19
    @52
    wph
    cK
    ctop
    wcel
    @53
    cvmlift2lem9a.k
    cK
    cY
    cvmlift2lem9a.y
    toptopon
    sylib
    cvmlift2lem9a.4
    cM
    cK
    cY
    resttopon
    syl2anc
    @44
    vx
    @4
    @0
    @1
    cM
    cW
    iscn
    syl2anc
    mpbir2and
    sseldd
end

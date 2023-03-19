include "ccnv.mm"
include "cdv.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "c1.mm"
include "cdiv.mm"
include "cc.mm"
include "cdm.mm"
include "wf.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "dvfg.mm"
include "syl.mm"
include "wss.mm"
include "recnprss.mm"
include "wf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "sstrd.mm"
include "fssd.mm"
include "ctopon.mm"
include "crest.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "toponss.mm"
include "syl2anc.mm"
include "dvbss.mm"
include "wa.mm"
include "wbr.mm"
include "wceq.mm"
include "f1ocnvfv2.mm"
include "sylan.mm"
include "adantr.mm"
include "ccncf.mm"
include "cc0.mm"
include "crn.mm"
include "wn.mm"
include "ffvelrnda.mm"
include "dvcnvlem.mm"
include "eqbrtrrd.mm"
include "reldv.mm"
include "releldmi.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "feqmptd.mm"
include "wfun.mm"
include "ffun.mm"
include "funbrfv.mm"
include "sylc.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem dvcnv
  let wph: wff ph
  let vx: setvar x
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume dvcnv.j: |- J = ( TopOpen ` CCfld )
  assume dvcnv.k: |- K = ( J |`t S )
  assume dvcnv.s: |- ( ph -> S e. { RR , CC } )
  assume dvcnv.y: |- ( ph -> Y e. K )
  assume dvcnv.f: |- ( ph -> F : X -1-1-onto-> Y )
  assume dvcnv.i: |- ( ph -> `' F e. ( Y -cn-> X ) )
  assume dvcnv.d: |- ( ph -> dom ( S _D F ) = X )
  assume dvcnv.z: |- ( ph -> -. 0 e. ran ( S _D F ) )

  disjoint F x
  disjoint J x
  disjoint ph x
  disjoint S x
  disjoint Y x
  disjoint x y
  disjoint x z
  disjoint C x
  disjoint y z
  disjoint C y
  disjoint C z
  disjoint F y
  disjoint F z
  disjoint J y
  disjoint J z
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint X y
  disjoint X z
  disjoint Y z
  assert |- ( ph -> ( S _D `' F ) = ( x e. Y |-> ( 1 / ( ( S _D F ) ` ( `' F ` x ) ) ) ) )

  proof
    wph
    cS
    cF
    ccnv
    #
    cdv
    co
    #
    vx
    cY
    vx
    cv
    #
    @1
    cfv
    #
    cmpt
    vx
    cY
    c1
    @2
    @0
    cfv
    #
    cS
    cF
    cdv
    co
    #
    cfv
    cdiv
    co
    #
    cmpt
    wph
    vx
    cY
    cc
    @1
    wph
    @1
    cdm
    #
    cc
    @1
    wf
    #
    cY
    cc
    @1
    wf
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @8
    dvcnv.s
    cS
    @0
    dvfg
    syl
    #
    wph
    @7
    cY
    cc
    @1
    wph
    @7
    cY
    wph
    cY
    cS
    @0
    wph
    @9
    cS
    cc
    wss
    #
    dvcnv.s
    cS
    recnprss
    syl
    #
    wph
    cY
    cX
    cc
    @0
    wph
    cX
    cY
    cF
    wf1o
    #
    cY
    cX
    @0
    wf1o
    cY
    cX
    @0
    wf
    dvcnv.f
    cX
    cY
    cF
    f1ocnv
    cY
    cX
    @0
    f1of
    3syl
    #
    wph
    cX
    cS
    cc
    wph
    cX
    @5
    cdm
    #
    cS
    dvcnv.d
    cS
    cF
    dvbsss
    syl6eqssr
    @12
    sstrd
    fssd
    wph
    cK
    cS
    ctopon
    cfv
    #
    wcel
    cY
    cK
    wcel
    #
    cY
    cS
    wss
    wph
    cK
    cJ
    cS
    crest
    co
    #
    @16
    dvcnv.k
    wph
    cJ
    cc
    ctopon
    cfv
    wcel
    @11
    @18
    @16
    wcel
    cJ
    dvcnv.j
    cnfldtopon
    @12
    cS
    cJ
    cc
    resttopon
    sylancr
    syl5eqel
    dvcnv.y
    cY
    cK
    cS
    toponss
    syl2anc
    dvbss
    wph
    vx
    cY
    @7
    wph
    @2
    cY
    wcel
    #
    @2
    @7
    wcel
    #
    wph
    @19
    wa
    #
    @2
    @6
    @1
    wbr
    #
    @20
    @21
    @4
    cF
    cfv
    #
    @2
    @6
    @1
    wph
    @13
    @19
    @23
    @2
    wceq
    dvcnv.f
    cX
    cY
    @2
    cF
    f1ocnvfv2
    sylan
    @21
    @4
    cS
    cF
    cJ
    cK
    cX
    cY
    dvcnv.j
    dvcnv.k
    wph
    @9
    @19
    dvcnv.s
    adantr
    wph
    @17
    @19
    dvcnv.y
    adantr
    wph
    @13
    @19
    dvcnv.f
    adantr
    wph
    @0
    cY
    cX
    ccncf
    co
    wcel
    @19
    dvcnv.i
    adantr
    wph
    @15
    cX
    wceq
    @19
    dvcnv.d
    adantr
    wph
    cc0
    @5
    crn
    wcel
    wn
    @19
    dvcnv.z
    adantr
    wph
    cY
    cX
    @2
    @0
    @14
    ffvelrnda
    dvcnvlem
    eqbrtrrd
    #
    @2
    @6
    @1
    cS
    @0
    reldv
    releldmi
    syl
    ex
    ssrdv
    eqssd
    feq2d
    mpbid
    feqmptd
    wph
    vx
    cY
    @3
    @6
    @21
    @1
    wfun
    #
    @22
    @3
    @6
    wceq
    @21
    @8
    @25
    wph
    @8
    @19
    @10
    adantr
    @7
    cc
    @1
    ffun
    syl
    @24
    @2
    @6
    @1
    funbrfv
    sylc
    mpteq2dva
    eqtrd
end

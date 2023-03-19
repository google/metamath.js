include "cv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "co.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cbl.mm"
include "cfv.mm"
include "cmul.mm"
include "cme.mm"
include "cr.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "metcl.mm"
include "syl3anc.mm"
include "simplrr.mm"
include "rpred.mm"
include "ltmuldiv2d.mm"
include "cle.mm"
include "anassrs.mm"
include "adantlrr.mm"
include "wi.mm"
include "remulcld.mm"
include "lelttr.mm"
include "mpand.mm"
include "sylbird.mm"
include "ss2rabdv.mm"
include "cxmt.mm"
include "cxr.mm"
include "wceq.mm"
include "metxmet.mm"
include "syl.mm"
include "adantr.mm"
include "simprl.mm"
include "rpdivcl.mm"
include "syl2anr.mm"
include "rpxrd.mm"
include "blval.mm"
include "rpxr.mm"
include "ad2antll.mm"
include "3sstr4d.mm"

theorem metss2lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cJ: class J
  let cK: class K
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  assume metequiv.3: |- J = ( MetOpen ` C )
  assume metequiv.4: |- K = ( MetOpen ` D )
  assume metss2.1: |- ( ph -> C e. ( Met ` X ) )
  assume metss2.2: |- ( ph -> D e. ( Met ` X ) )
  assume metss2.3: |- ( ph -> R e. RR+ )
  assume metss2.4: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x C y ) <_ ( R x. ( x D y ) ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint R y
  disjoint S y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint J r
  disjoint J s
  disjoint K r
  disjoint K s
  disjoint R s
  disjoint D r
  disjoint D s
  disjoint D z
  disjoint ph r
  disjoint X r
  disjoint X s
  disjoint X z
  disjoint a b
  disjoint a x
  disjoint C a
  disjoint b x
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint J a
  disjoint J b
  disjoint K a
  disjoint K b
  disjoint X a
  disjoint X b
  assert |- ( ( ph /\ ( x e. X /\ S e. RR+ ) ) -> ( x ( ball ` D ) ( S / R ) ) C_ ( x ( ball ` C ) S ) )

  proof
    wph
    vx
    cv
    #
    cX
    wcel
    #
    cS
    crp
    wcel
    #
    wa
    #
    wa
    #
    @0
    vy
    cv
    #
    cD
    co
    #
    cS
    cR
    cdiv
    co
    #
    clt
    wbr
    #
    vy
    cX
    crab
    #
    @0
    @5
    cC
    co
    #
    cS
    clt
    wbr
    #
    vy
    cX
    crab
    #
    @0
    @7
    cD
    cbl
    cfv
    co
    #
    @0
    cS
    cC
    cbl
    cfv
    co
    #
    @4
    @8
    @11
    vy
    cX
    @4
    @5
    cX
    wcel
    #
    wa
    #
    @8
    cR
    @6
    cmul
    co
    #
    cS
    clt
    wbr
    #
    @11
    @16
    @6
    cS
    cR
    @16
    cD
    cX
    cme
    cfv
    #
    wcel
    #
    @1
    @15
    @6
    cr
    wcel
    wph
    @20
    @3
    @15
    metss2.2
    ad2antrr
    wph
    @1
    @2
    @15
    simplrl
    #
    @4
    @15
    simpr
    #
    @0
    @5
    cD
    cX
    metcl
    syl3anc
    #
    @16
    cS
    wph
    @1
    @2
    @15
    simplrr
    rpred
    #
    wph
    cR
    crp
    wcel
    #
    @3
    @15
    metss2.3
    ad2antrr
    #
    ltmuldiv2d
    @16
    @10
    @17
    cle
    wbr
    #
    @18
    @11
    wph
    @1
    @15
    @27
    @2
    wph
    @1
    @15
    @27
    metss2.4
    anassrs
    adantlrr
    @16
    @10
    cr
    wcel
    #
    @17
    cr
    wcel
    cS
    cr
    wcel
    @27
    @18
    wa
    @11
    wi
    @16
    cC
    @19
    wcel
    #
    @1
    @15
    @28
    wph
    @29
    @3
    @15
    metss2.1
    ad2antrr
    @21
    @22
    @0
    @5
    cC
    cX
    metcl
    syl3anc
    @16
    cR
    @6
    @16
    cR
    @26
    rpred
    @23
    remulcld
    @24
    @10
    @17
    cS
    lelttr
    syl3anc
    mpand
    sylbird
    ss2rabdv
    @4
    cD
    cX
    cxmt
    cfv
    #
    wcel
    #
    @1
    @7
    cxr
    wcel
    @13
    @9
    wceq
    wph
    @31
    @3
    wph
    @20
    @31
    metss2.2
    cD
    cX
    metxmet
    syl
    adantr
    wph
    @1
    @2
    simprl
    #
    @4
    @7
    @3
    @2
    @25
    @7
    crp
    wcel
    wph
    @1
    @2
    simpr
    metss2.3
    cS
    cR
    rpdivcl
    syl2anr
    rpxrd
    vy
    cD
    @0
    @7
    cX
    blval
    syl3anc
    @4
    cC
    @30
    wcel
    #
    @1
    cS
    cxr
    wcel
    #
    @14
    @12
    wceq
    wph
    @33
    @3
    wph
    @29
    @33
    metss2.1
    cC
    cX
    metxmet
    syl
    adantr
    @32
    @2
    @34
    wph
    @1
    cS
    rpxr
    ad2antll
    vy
    cC
    @0
    cS
    cX
    blval
    syl3anc
    3sstr4d
end

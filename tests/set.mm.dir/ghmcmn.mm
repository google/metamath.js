include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "ccmn.mm"
include "cmnmnd.mm"
include "syl.mm"
include "mhmmnd.mm"
include "wa.mm"
include "cfv.mm"
include "simp-6l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "cmncom.mm"
include "syl3anc.mm"
include "fveq2d.mm"
include "syl3an1.mm"
include "mhmlem.mm"
include "3eqtr3d.mm"
include "simpllr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "wrex.mm"
include "wfo.mm"
include "foelrni.mm"
include "sylan.mm"
include "adantlr.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "adantr.mm"
include "anasss.mm"
include "ralrimivva.mm"
include "iscmn.mm"
include "sylanbrc.mm"

theorem ghmcmn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.pd: class .+^
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  assume ghmabl.x: |- X = ( Base ` G )
  assume ghmabl.y: |- Y = ( Base ` H )
  assume ghmabl.p: |- .+ = ( +g ` G )
  assume ghmabl.q: |- .+^ = ( +g ` H )
  assume ghmabl.f: |- ( ( ph /\ x e. X /\ y e. X ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )
  assume ghmabl.1: |- ( ph -> F : X -onto-> Y )
  assume ghmcmn.3: |- ( ph -> G e. CMnd )

  disjoint .+ x
  disjoint .+ y
  disjoint x y
  disjoint .+^ x
  disjoint .+^ y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint .+^ a
  disjoint .+^ b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint F a
  disjoint F b
  disjoint H i
  disjoint H j
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  disjoint Y i
  disjoint Y j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> H e. CMnd )

  proof
    wph
    cH
    cmnd
    wcel
    vi
    cv
    #
    vj
    cv
    #
    c.pd
    co
    #
    @1
    @0
    c.pd
    co
    #
    wceq
    #
    vj
    cY
    wral
    vi
    cY
    wral
    cH
    ccmn
    wcel
    wph
    vx
    vy
    c.pl
    c.pd
    cF
    cG
    cH
    cX
    cY
    ghmabl.f
    ghmabl.x
    ghmabl.y
    ghmabl.p
    ghmabl.q
    ghmabl.1
    wph
    cG
    ccmn
    wcel
    #
    cG
    cmnd
    wcel
    ghmcmn.3
    cG
    cmnmnd
    syl
    mhmmnd
    wph
    @4
    vi
    vj
    cY
    cY
    wph
    @0
    cY
    wcel
    #
    @1
    cY
    wcel
    #
    @4
    wph
    @6
    wa
    #
    @7
    wa
    #
    va
    cv
    #
    cF
    cfv
    #
    @0
    wceq
    #
    @4
    va
    cX
    @9
    @10
    cX
    wcel
    #
    wa
    #
    @12
    wa
    #
    vb
    cv
    #
    cF
    cfv
    #
    @1
    wceq
    #
    @4
    vb
    cX
    @15
    @16
    cX
    wcel
    #
    wa
    #
    @18
    wa
    #
    @11
    @17
    c.pd
    co
    #
    @17
    @11
    c.pd
    co
    #
    @2
    @3
    @21
    @10
    @16
    c.pl
    co
    #
    cF
    cfv
    @16
    @10
    c.pl
    co
    #
    cF
    cfv
    @22
    @23
    @21
    @24
    @25
    cF
    @21
    @5
    @13
    @19
    @24
    @25
    wceq
    @21
    wph
    @5
    wph
    @6
    @7
    @13
    @12
    @19
    @18
    simp-6l
    #
    ghmcmn.3
    syl
    @9
    @13
    @12
    @19
    @18
    simp-4r
    #
    @15
    @19
    @18
    simplr
    #
    cX
    c.pl
    cG
    @10
    @16
    ghmabl.x
    ghmabl.p
    cmncom
    syl3anc
    fveq2d
    @21
    vx
    vy
    @10
    @16
    c.pl
    c.pd
    cF
    cX
    @21
    wph
    vx
    cv
    #
    cX
    wcel
    vy
    cv
    #
    cX
    wcel
    @29
    @30
    c.pl
    co
    cF
    cfv
    @29
    cF
    cfv
    @30
    cF
    cfv
    c.pd
    co
    wceq
    @26
    ghmabl.f
    syl3an1
    #
    @27
    @28
    mhmlem
    @21
    vx
    vy
    @16
    @10
    c.pl
    c.pd
    cF
    cX
    @31
    @28
    @27
    mhmlem
    3eqtr3d
    @21
    @11
    @0
    @17
    @1
    c.pd
    @14
    @12
    @19
    @18
    simpllr
    #
    @20
    @18
    simpr
    #
    oveq12d
    @21
    @17
    @1
    @11
    @0
    c.pd
    @33
    @32
    oveq12d
    3eqtr3d
    @9
    @18
    vb
    cX
    wrex
    #
    @13
    @12
    wph
    @7
    @34
    @6
    wph
    cX
    cY
    cF
    wfo
    #
    @7
    @34
    ghmabl.1
    vb
    cX
    cY
    cF
    @1
    foelrni
    sylan
    adantlr
    ad2antrr
    r19.29a
    @8
    @12
    va
    cX
    wrex
    #
    @7
    wph
    @35
    @6
    @36
    ghmabl.1
    va
    cX
    cY
    cF
    @0
    foelrni
    sylan
    adantr
    r19.29a
    anasss
    ralrimivva
    vi
    vj
    cY
    c.pd
    cH
    ghmabl.y
    ghmabl.q
    iscmn
    sylanbrc
end

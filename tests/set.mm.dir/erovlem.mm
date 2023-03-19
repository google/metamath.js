include "cv.mm"
include "cec.mm"
include "wceq.mm"
include "wa.mm"
include "co.mm"
include "wrex.mm"
include "coprab.mm"
include "wcel.mm"
include "cio.mm"
include "cmpt2.mm"
include "simpl.mm"
include "reximi.mm"
include "cqs.mm"
include "eleq2i.mm"
include "vex.mm"
include "elqs.mm"
include "bitri.mm"
include "anbi12i.mm"
include "reeanv.mm"
include "bitr4i.mm"
include "sylibr.mm"
include "pm4.71ri.mm"
include "weu.mm"
include "wb.mm"
include "eroveu.mm"
include "iota1.mm"
include "syl.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "oprabbidv.mm"
include "df-mpt2.mm"
include "nfv.mm"
include "nfiota1.mm"
include "nfeq2.mm"
include "nfan.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "cbvoprab3.mm"
include "eqtr4i.mm"
include "3eqtr4g.mm"

theorem erovlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  let vw: setvar w
  let cL: class L
  let cP: class P
  let cQ: class Q
  let cX: class X
  let cY: class Y
  assume eropr.1: |- J = ( A /. R )
  assume eropr.2: |- K = ( B /. S )
  assume eropr.3: |- ( ph -> T e. Z )
  assume eropr.4: |- ( ph -> R Er U )
  assume eropr.5: |- ( ph -> S Er V )
  assume eropr.6: |- ( ph -> T Er W )
  assume eropr.7: |- ( ph -> A C_ U )
  assume eropr.8: |- ( ph -> B C_ V )
  assume eropr.9: |- ( ph -> C C_ W )
  assume eropr.10: |- ( ph -> .+ : ( A X. B ) --> C )
  assume eropr.11: |- ( ( ph /\ ( ( r e. A /\ s e. A ) /\ ( t e. B /\ u e. B ) ) ) -> ( ( r R s /\ t S u ) -> ( r .+ t ) T ( s .+ u ) ) )
  assume eropr.12: |- .+^ = { <. <. x , y >. , z >. | E. p e. A E. q e. B ( ( x = [ p ] R /\ y = [ q ] S ) /\ z = [ ( p .+ q ) ] T ) }

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint q t
  disjoint q u
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s t
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B p
  disjoint B q
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint J p
  disjoint J q
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint R p
  disjoint R q
  disjoint R r
  disjoint R s
  disjoint R t
  disjoint R u
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint K p
  disjoint K q
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint .+ p
  disjoint .+ q
  disjoint .+ r
  disjoint .+ s
  disjoint .+ t
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint T p
  disjoint T q
  disjoint T r
  disjoint T s
  disjoint T t
  disjoint T u
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint p w
  disjoint q w
  disjoint r w
  disjoint s w
  disjoint t w
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B w
  disjoint L p
  disjoint L q
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint J w
  disjoint P p
  disjoint P q
  disjoint P r
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R w
  disjoint K w
  disjoint Q p
  disjoint Q q
  disjoint Q r
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint S w
  disjoint .+ w
  disjoint ph w
  disjoint T w
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X z
  disjoint Y p
  disjoint Y q
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> .+^ = ( x e. J , y e. K |-> ( iota z E. p e. A E. q e. B ( ( x = [ p ] R /\ y = [ q ] S ) /\ z = [ ( p .+ q ) ] T ) ) ) )

  proof
    wph
    vx
    cv
    #
    vp
    cv
    #
    cR
    cec
    wceq
    #
    vy
    cv
    #
    vq
    cv
    #
    cS
    cec
    wceq
    #
    wa
    #
    vz
    cv
    #
    @1
    @4
    c.pl
    co
    cT
    cec
    wceq
    #
    wa
    #
    vq
    cB
    wrex
    #
    vp
    cA
    wrex
    #
    vx
    vy
    vz
    coprab
    @0
    cJ
    wcel
    #
    @3
    cK
    wcel
    #
    wa
    #
    @7
    @11
    vz
    cio
    #
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    c.pd
    vx
    vy
    cJ
    cK
    @15
    cmpt2
    #
    wph
    @11
    @17
    vx
    vy
    vz
    @11
    @14
    @11
    wa
    wph
    @17
    @11
    @14
    @11
    @6
    vq
    cB
    wrex
    #
    vp
    cA
    wrex
    #
    @14
    @10
    @20
    vp
    cA
    @9
    @6
    vq
    cB
    @6
    @8
    simpl
    reximi
    reximi
    @14
    @2
    vp
    cA
    wrex
    #
    @5
    vq
    cB
    wrex
    #
    wa
    @21
    @12
    @22
    @13
    @23
    @12
    @0
    cA
    cR
    cqs
    #
    wcel
    @22
    cJ
    @24
    @0
    eropr.1
    eleq2i
    vp
    cA
    @0
    cR
    vx
    vex
    elqs
    bitri
    @13
    @3
    cB
    cS
    cqs
    #
    wcel
    @23
    cK
    @25
    @3
    eropr.2
    eleq2i
    vq
    cB
    @3
    cS
    vy
    vex
    elqs
    bitri
    anbi12i
    @2
    @5
    vp
    vq
    cA
    cB
    reeanv
    bitr4i
    sylibr
    pm4.71ri
    wph
    @14
    @11
    @16
    wph
    @14
    wa
    #
    @11
    @15
    @7
    wceq
    #
    @16
    @26
    @11
    vz
    weu
    @11
    @27
    wb
    wph
    vz
    vu
    vt
    cA
    cB
    cC
    c.pl
    cR
    cS
    cT
    cU
    cJ
    cK
    cV
    cW
    @0
    @3
    cZ
    vs
    vr
    vq
    vp
    eropr.1
    eropr.2
    eropr.3
    eropr.4
    eropr.5
    eropr.6
    eropr.7
    eropr.8
    eropr.9
    eropr.10
    eropr.11
    eroveu
    @11
    vz
    iota1
    syl
    @15
    @7
    eqcom
    syl6bb
    pm5.32da
    syl5bb
    oprabbidv
    eropr.12
    @19
    @14
    vw
    cv
    #
    @15
    wceq
    #
    wa
    #
    vx
    vy
    vw
    coprab
    @18
    vx
    vy
    vw
    cJ
    cK
    @15
    df-mpt2
    @17
    @30
    vx
    vy
    vz
    vw
    @17
    vw
    nfv
    @14
    @29
    vz
    @14
    vz
    nfv
    vz
    @28
    @15
    @11
    vz
    nfiota1
    nfeq2
    nfan
    @7
    @28
    wceq
    @16
    @29
    @14
    @7
    @28
    @15
    eqeq1
    anbi2d
    cbvoprab3
    eqtr4i
    3eqtr4g
end

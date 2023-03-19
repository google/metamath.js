include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "wf1.mm"
include "wral.mm"
include "cfth.mm"
include "funcsetcestrc.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "funcsetcestrclem8.mm"
include "cmap.mm"
include "cwun.mm"
include "adantr.mm"
include "eqid.mm"
include "cbs.mm"
include "setcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "adantl.mm"
include "setchom.mm"
include "funcsetcestrclem6.mm"
include "3expia.mm"
include "sylbid.mm"
include "com12.mm"
include "eqeq12d.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "isfth2.mm"

theorem fthsetcestrc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  let vk: setvar k
  assume funcsetcestrc.s: |- S = ( SetCat ` U )
  assume funcsetcestrc.c: |- C = ( Base ` S )
  assume funcsetcestrc.f: |- ( ph -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) )
  assume funcsetcestrc.u: |- ( ph -> U e. WUni )
  assume funcsetcestrc.o: |- ( ph -> _om e. U )
  assume funcsetcestrc.g: |- ( ph -> G = ( x e. C , y e. C |-> ( _I |` ( y ^m x ) ) ) )
  assume funcsetcestrc.e: |- E = ( ExtStrCat ` U )

  disjoint C x
  disjoint ph x
  disjoint C y
  disjoint x y
  disjoint ph y
  disjoint E x
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint C f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  disjoint Z x
  disjoint Z y
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C h
  disjoint C k
  disjoint a h
  disjoint a k
  disjoint b h
  disjoint b k
  disjoint c h
  disjoint c k
  disjoint h k
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E h
  disjoint E k
  disjoint h x
  disjoint k x
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F h
  disjoint F k
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G h
  disjoint G k
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S h
  disjoint S k
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint h ph
  disjoint k ph
  assert |- ( ph -> F ( S Faith E ) G )

  proof
    wph
    cF
    cG
    cS
    cE
    cfunc
    co
    wbr
    va
    cv
    #
    vb
    cv
    #
    cS
    chom
    cfv
    #
    co
    #
    @0
    cF
    cfv
    @1
    cF
    cfv
    cE
    chom
    cfv
    #
    co
    #
    @0
    @1
    cG
    co
    #
    wf1
    #
    vb
    cC
    wral
    va
    cC
    wral
    cF
    cG
    cS
    cE
    cfth
    co
    wbr
    wph
    vx
    vy
    cC
    cS
    cU
    cE
    cF
    cG
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrc.e
    funcsetcestrc
    wph
    @7
    va
    vb
    cC
    cC
    wph
    @0
    cC
    wcel
    #
    @1
    cC
    wcel
    #
    wa
    #
    wa
    #
    @3
    @5
    @6
    wf
    vh
    cv
    #
    @6
    cfv
    #
    vk
    cv
    #
    @6
    cfv
    #
    wceq
    #
    vh
    vk
    weq
    #
    wi
    #
    vk
    @3
    wral
    vh
    @3
    wral
    @7
    wph
    vx
    vy
    cC
    cS
    cU
    cE
    cF
    cG
    @0
    @1
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrc.e
    funcsetcestrclem8
    @11
    @18
    vh
    vk
    @3
    @3
    @11
    @12
    @3
    wcel
    #
    @14
    @3
    wcel
    #
    wa
    #
    wa
    #
    @16
    @17
    @22
    @13
    @12
    @15
    @14
    @21
    @11
    @13
    @12
    wceq
    #
    @19
    @11
    @23
    wi
    @20
    @11
    @19
    @23
    @11
    @19
    @12
    @1
    @0
    cmap
    co
    #
    wcel
    #
    @23
    @11
    @3
    @24
    @12
    @11
    cS
    cU
    @2
    cwun
    @0
    @1
    funcsetcestrc.s
    wph
    cU
    cwun
    wcel
    @10
    funcsetcestrc.u
    adantr
    @2
    eqid
    #
    @10
    wph
    @0
    cU
    wcel
    #
    @8
    wph
    @27
    wi
    @9
    wph
    @8
    @27
    wph
    cC
    cU
    @0
    wph
    cU
    cS
    cbs
    cfv
    cC
    wph
    cS
    cU
    cwun
    funcsetcestrc.s
    funcsetcestrc.u
    setcbas
    funcsetcestrc.c
    syl6reqr
    #
    eleq2d
    biimpcd
    adantr
    impcom
    @10
    wph
    @1
    cU
    wcel
    #
    @9
    wph
    @29
    wi
    @8
    wph
    @9
    @29
    wph
    cC
    cU
    @1
    @28
    eleq2d
    biimpcd
    adantl
    impcom
    setchom
    #
    eleq2d
    wph
    @10
    @25
    @23
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    @12
    @0
    @1
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem6
    3expia
    sylbid
    com12
    adantr
    impcom
    @21
    @11
    @15
    @14
    wceq
    #
    @20
    @11
    @31
    wi
    @19
    @11
    @20
    @31
    @11
    @20
    @14
    @24
    wcel
    #
    @31
    @11
    @3
    @24
    @14
    @30
    eleq2d
    wph
    @10
    @32
    @31
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    @14
    @0
    @1
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem6
    3expia
    sylbid
    com12
    adantl
    impcom
    eqeq12d
    biimpd
    ralrimivva
    vh
    vk
    @3
    @5
    @6
    dff13
    sylanbrc
    ralrimivva
    va
    vb
    cC
    cS
    cE
    cF
    cG
    @2
    @4
    funcsetcestrc.c
    @26
    @4
    eqid
    isfth2
    sylanbrc
end

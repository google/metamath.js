include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "wf1.mm"
include "wral.mm"
include "cfth.mm"
include "funcestrcsetc.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "funcestrcsetclem8.mm"
include "cbs.mm"
include "cmap.mm"
include "cwun.mm"
include "adantr.mm"
include "eqid.mm"
include "estrcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "adantl.mm"
include "estrchom.mm"
include "funcestrcsetclem6.mm"
include "3expia.mm"
include "sylbid.mm"
include "com12.mm"
include "eqeq12d.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "isfth2.mm"

theorem fthestrcsetc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let vf: setvar f
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  let vk: setvar k
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcestrcsetc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( ( Base ` y ) ^m ( Base ` x ) ) ) ) )

  disjoint B x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint B f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint Y x
  disjoint Y y
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
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B h
  disjoint B k
  disjoint a h
  disjoint a k
  disjoint b h
  disjoint b k
  disjoint c h
  disjoint c k
  disjoint h k
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
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E h
  disjoint E k
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
  assert |- ( ph -> F ( E Faith S ) G )

  proof
    wph
    cF
    cG
    cE
    cS
    cfunc
    co
    wbr
    va
    cv
    #
    vb
    cv
    #
    cE
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
    cS
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
    cB
    wral
    va
    cB
    wral
    cF
    cG
    cE
    cS
    cfth
    co
    wbr
    wph
    vx
    vy
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    funcestrcsetc
    wph
    @7
    va
    vb
    cB
    cB
    wph
    @0
    cB
    wcel
    #
    @1
    cB
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
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    @0
    @1
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    funcestrcsetclem8
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
    cbs
    cfv
    #
    @0
    cbs
    cfv
    #
    cmap
    co
    #
    wcel
    #
    @23
    @11
    @3
    @26
    @12
    @11
    @25
    @24
    cE
    cU
    @2
    cwun
    @0
    @1
    funcestrcsetc.e
    wph
    cU
    cwun
    wcel
    @10
    funcestrcsetc.u
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
    @29
    wi
    @9
    wph
    @8
    @29
    wph
    cB
    cU
    @0
    wph
    cU
    cE
    cbs
    cfv
    cB
    wph
    cE
    cU
    cwun
    funcestrcsetc.e
    funcestrcsetc.u
    estrcbas
    funcestrcsetc.b
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
    @31
    wi
    @8
    wph
    @9
    @31
    wph
    cB
    cU
    @1
    @30
    eleq2d
    biimpcd
    adantl
    impcom
    @25
    eqid
    #
    @24
    eqid
    #
    estrchom
    #
    eleq2d
    wph
    @10
    @27
    @23
    wph
    vx
    vy
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    @12
    @25
    @24
    @0
    @1
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @32
    @33
    funcestrcsetclem6
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
    @35
    wi
    @19
    @11
    @20
    @35
    @11
    @20
    @14
    @26
    wcel
    #
    @35
    @11
    @3
    @26
    @14
    @34
    eleq2d
    wph
    @10
    @36
    @35
    wph
    vx
    vy
    cB
    cC
    cS
    cU
    cE
    cF
    cG
    @14
    @25
    @24
    @0
    @1
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @32
    @33
    funcestrcsetclem6
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
    cB
    cE
    cS
    cF
    cG
    @2
    @4
    funcestrcsetc.b
    @28
    @4
    eqid
    isfth2
    sylanbrc
end

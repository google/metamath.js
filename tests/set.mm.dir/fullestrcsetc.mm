include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "wfo.mm"
include "wral.mm"
include "cful.mm"
include "funcestrcsetc.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wceq.mm"
include "wrex.mm"
include "funcestrcsetclem8.mm"
include "cbs.mm"
include "cwun.mm"
include "adantr.mm"
include "eqid.mm"
include "funcestrcsetclem2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "elsetchom.mm"
include "funcestrcsetclem1.mm"
include "feq23d.mm"
include "bitrd.mm"
include "cmap.mm"
include "weq.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "biimpar.mm"
include "equequ2.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "funcestrcsetclem6.mm"
include "3expa.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "wi.mm"
include "estrcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "estrchom.mm"
include "rexeqdv.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "dffo3.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "isfull2.mm"

theorem fullestrcsetc
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
  assert |- ( ph -> F ( E Full S ) G )

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
    #
    @1
    cF
    cfv
    #
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
    wfo
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
    cful
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
    @9
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
    @7
    @8
    wf
    vh
    cv
    #
    vk
    cv
    #
    @8
    cfv
    #
    wceq
    #
    vk
    @3
    wrex
    #
    vh
    @7
    wral
    @9
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
    @13
    @18
    vh
    @7
    @13
    @14
    @7
    wcel
    #
    @0
    cbs
    cfv
    #
    @1
    cbs
    cfv
    #
    @14
    wf
    #
    @18
    @13
    @19
    @4
    @5
    @14
    wf
    @22
    @13
    cS
    cU
    @14
    @6
    cwun
    @4
    @5
    funcestrcsetc.s
    wph
    cU
    cwun
    wcel
    @12
    funcestrcsetc.u
    adantr
    #
    @6
    eqid
    #
    wph
    @10
    @4
    cU
    wcel
    @11
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    @0
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem2
    adantrr
    wph
    @11
    @5
    cU
    wcel
    @10
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    @1
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem2
    adantrl
    elsetchom
    @13
    @4
    @5
    @20
    @21
    @14
    wph
    @10
    @4
    @20
    wceq
    @11
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    @0
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    adantrr
    wph
    @11
    @5
    @21
    wceq
    @10
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    @1
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    adantrl
    feq23d
    bitrd
    @13
    @22
    @18
    @13
    @22
    wa
    #
    @18
    @17
    vk
    @21
    @20
    cmap
    co
    #
    wrex
    #
    @25
    @27
    vh
    vk
    weq
    #
    vk
    @26
    wrex
    #
    @25
    @28
    vh
    vh
    weq
    #
    vk
    @14
    @26
    @13
    @14
    @26
    wcel
    #
    @22
    @21
    cvv
    wcel
    #
    @20
    cvv
    wcel
    #
    wa
    @31
    @22
    wb
    @13
    @32
    @33
    @1
    cbs
    fvex
    @0
    cbs
    fvex
    pm3.2i
    @21
    @20
    @14
    cvv
    cvv
    elmapg
    mp1i
    biimpar
    vk
    vh
    weq
    @28
    @30
    wb
    @25
    vk
    vh
    vh
    equequ2
    adantl
    @25
    @14
    eqidd
    rspcedvd
    @13
    @27
    @29
    wb
    @22
    @13
    @17
    @28
    vk
    @26
    @13
    @15
    @26
    wcel
    #
    wa
    @16
    @15
    @14
    wph
    @12
    @34
    @16
    @15
    wceq
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
    @15
    @20
    @21
    @0
    @1
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @20
    eqid
    #
    @21
    eqid
    #
    funcestrcsetclem6
    3expa
    eqeq2d
    rexbidva
    adantr
    mpbird
    @13
    @18
    @27
    wb
    @22
    @13
    @17
    vk
    @3
    @26
    @13
    @20
    @21
    cE
    cU
    @2
    cwun
    @0
    @1
    funcestrcsetc.e
    @23
    @2
    eqid
    #
    @12
    wph
    @0
    cU
    wcel
    #
    @10
    wph
    @38
    wi
    @11
    wph
    @10
    @38
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
    @12
    wph
    @1
    cU
    wcel
    #
    @11
    wph
    @40
    wi
    @10
    wph
    @11
    @40
    wph
    cB
    cU
    @1
    @39
    eleq2d
    biimpcd
    adantl
    impcom
    @35
    @36
    estrchom
    rexeqdv
    adantr
    mpbird
    ex
    sylbid
    ralrimiv
    vk
    vh
    @3
    @7
    @8
    dffo3
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
    @6
    funcestrcsetc.b
    @24
    @37
    isfull2
    sylanbrc
end

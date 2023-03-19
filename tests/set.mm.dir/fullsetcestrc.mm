include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "chom.mm"
include "cfv.mm"
include "wfo.mm"
include "wral.mm"
include "cful.mm"
include "funcsetcestrc.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "wceq.mm"
include "wrex.mm"
include "funcsetcestrclem8.mm"
include "cbs.mm"
include "cwun.mm"
include "adantr.mm"
include "eqid.mm"
include "funcsetcestrclem2.mm"
include "adantrr.mm"
include "adantrl.mm"
include "elestrchom.mm"
include "cnx.mm"
include "cop.mm"
include "csn.mm"
include "funcsetcestrclem1.mm"
include "fveq2d.mm"
include "1strbas.mm"
include "ad2antrl.mm"
include "eqtr4d.mm"
include "ad2antll.mm"
include "feq23d.mm"
include "cmap.mm"
include "weq.mm"
include "wb.mm"
include "simpr.mm"
include "ancomd.mm"
include "elmapg.mm"
include "syl.mm"
include "biimpar.mm"
include "equequ2.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "funcsetcestrclem6.mm"
include "3expa.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "wi.mm"
include "setcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "setchom.mm"
include "rexeqdv.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "dffo3.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "isfull2.mm"

theorem fullsetcestrc
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
  assert |- ( ph -> F ( S Full E ) G )

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
    #
    @1
    cF
    cfv
    #
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
    wfo
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
    cful
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
    @9
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
    @13
    @18
    vh
    @7
    @13
    @14
    @7
    wcel
    @4
    cbs
    cfv
    #
    @5
    cbs
    cfv
    #
    @14
    wf
    #
    @18
    @13
    @19
    @20
    cE
    cU
    @14
    @6
    cwun
    @4
    @5
    funcsetcestrc.e
    wph
    cU
    cwun
    wcel
    @12
    funcsetcestrc.u
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
    cC
    cS
    cU
    cF
    @0
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrclem2
    adantrr
    wph
    @11
    @5
    cU
    wcel
    @10
    wph
    vx
    cC
    cS
    cU
    cF
    @1
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrclem2
    adantrl
    @19
    eqid
    @20
    eqid
    elestrchom
    @13
    @21
    @0
    @1
    @14
    wf
    #
    @18
    @13
    @19
    @20
    @0
    @1
    @14
    @13
    @19
    cnx
    cbs
    cfv
    #
    @0
    cop
    csn
    #
    cbs
    cfv
    #
    @0
    @13
    @4
    @26
    cbs
    wph
    @10
    @4
    @26
    wceq
    @11
    wph
    vx
    cC
    cS
    cU
    cF
    @0
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    adantrr
    fveq2d
    @10
    @0
    @27
    wceq
    wph
    @11
    @0
    @26
    cC
    @26
    eqid
    1strbas
    ad2antrl
    eqtr4d
    @13
    @20
    @25
    @1
    cop
    csn
    #
    cbs
    cfv
    #
    @1
    @13
    @5
    @28
    cbs
    wph
    @11
    @5
    @28
    wceq
    @10
    wph
    vx
    cC
    cS
    cU
    cF
    @1
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrclem1
    adantrl
    fveq2d
    @11
    @1
    @29
    wceq
    wph
    @10
    @1
    @28
    cC
    @28
    eqid
    1strbas
    ad2antll
    eqtr4d
    feq23d
    @13
    @24
    @18
    @13
    @24
    wa
    #
    @18
    @17
    vk
    @1
    @0
    cmap
    co
    #
    wrex
    #
    @30
    @32
    vh
    vk
    weq
    #
    vk
    @31
    wrex
    #
    @30
    @33
    vh
    vh
    weq
    #
    vk
    @14
    @31
    @13
    @14
    @31
    wcel
    #
    @24
    @13
    @11
    @10
    wa
    @36
    @24
    wb
    @13
    @10
    @11
    wph
    @12
    simpr
    ancomd
    @1
    @0
    @14
    cC
    cC
    elmapg
    syl
    biimpar
    vk
    vh
    weq
    @33
    @35
    wb
    @30
    vk
    vh
    vh
    equequ2
    adantl
    @30
    @14
    eqidd
    rspcedvd
    @13
    @32
    @34
    wb
    @24
    @13
    @17
    @33
    vk
    @31
    @13
    @15
    @31
    wcel
    #
    wa
    @16
    @15
    @14
    wph
    @12
    @37
    @16
    @15
    wceq
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    @15
    @0
    @1
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem6
    3expa
    eqeq2d
    rexbidva
    adantr
    mpbird
    @13
    @18
    @32
    wb
    @24
    @13
    @17
    vk
    @3
    @31
    @13
    cS
    cU
    @2
    cwun
    @0
    @1
    funcsetcestrc.s
    @22
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
    @39
    wi
    @11
    wph
    @10
    @39
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
    @12
    wph
    @1
    cU
    wcel
    #
    @11
    wph
    @41
    wi
    @10
    wph
    @11
    @41
    wph
    cC
    cU
    @1
    @40
    eleq2d
    biimpcd
    adantl
    impcom
    setchom
    rexeqdv
    adantr
    mpbird
    ex
    sylbid
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
    cC
    cS
    cE
    cF
    cG
    @2
    @6
    funcsetcestrc.c
    @23
    @38
    isfull2
    sylanbrc
end

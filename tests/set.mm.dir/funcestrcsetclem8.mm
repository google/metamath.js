include "wcel.mm"
include "wa.mm"
include "chom.mm"
include "cfv.mm"
include "co.mm"
include "wf.mm"
include "cbs.mm"
include "cmap.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "cv.mm"
include "elmapi.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "bicomd.mm"
include "biimpa.mm"
include "wceq.mm"
include "funcestrcsetclem1.mm"
include "adantrl.mm"
include "adantrr.mm"
include "oveq12d.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "ex.mm"
include "syl5.mm"
include "ssrdv.mm"
include "fssd.mm"
include "eqid.mm"
include "funcestrcsetclem5.mm"
include "cwun.mm"
include "wi.mm"
include "estrcbas.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "biimpd.mm"
include "adantld.mm"
include "imp.mm"
include "estrchom.mm"
include "funcestrcsetclem2.mm"
include "setchom.mm"
include "feq123d.mm"
include "mpbird.mm"

theorem funcestrcsetclem8
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
  let cY: class Y
  let vf: setvar f
  assume funcestrcsetc.e: |- E = ( ExtStrCat ` U )
  assume funcestrcsetc.s: |- S = ( SetCat ` U )
  assume funcestrcsetc.b: |- B = ( Base ` E )
  assume funcestrcsetc.c: |- C = ( Base ` S )
  assume funcestrcsetc.u: |- ( ph -> U e. WUni )
  assume funcestrcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcestrcsetc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( ( Base ` y ) ^m ( Base ` x ) ) ) ) )

  disjoint B x
  disjoint X x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint X y
  disjoint ph y
  disjoint Y x
  disjoint Y y
  disjoint B f
  disjoint F f
  disjoint X f
  disjoint Y f
  disjoint f ph
  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) ) -> ( X G Y ) : ( X ( Hom ` E ) Y ) --> ( ( F ` X ) ( Hom ` S ) ( F ` Y ) ) )

  proof
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cE
    chom
    cfv
    #
    co
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    cS
    chom
    cfv
    #
    co
    #
    cX
    cY
    cG
    co
    #
    wf
    cY
    cbs
    cfv
    #
    cX
    cbs
    cfv
    #
    cmap
    co
    #
    @7
    @6
    cmap
    co
    #
    cid
    @13
    cres
    #
    wf
    @3
    @13
    @13
    @14
    @15
    @13
    @13
    @15
    wf1o
    @13
    @13
    @15
    wf
    @3
    @13
    f1oi
    @13
    @13
    @15
    f1of
    mp1i
    @3
    vf
    @13
    @14
    vf
    cv
    #
    @13
    wcel
    #
    @12
    @11
    @16
    wf
    #
    @3
    @16
    @14
    wcel
    #
    @16
    @11
    @12
    elmapi
    @3
    @18
    @19
    @3
    @18
    wa
    @16
    @13
    @14
    @3
    @18
    @17
    @11
    cvv
    wcel
    #
    @12
    cvv
    wcel
    #
    wa
    #
    @18
    @17
    wb
    @3
    @20
    @21
    cY
    cbs
    fvex
    cX
    cbs
    fvex
    pm3.2i
    @22
    @17
    @18
    @11
    @12
    @16
    cvv
    cvv
    elmapg
    bicomd
    mp1i
    biimpa
    @3
    @14
    @13
    wceq
    @18
    @3
    @7
    @11
    @6
    @12
    cmap
    wph
    @1
    @7
    @11
    wceq
    @0
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cY
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    adantrl
    wph
    @0
    @6
    @12
    wceq
    @1
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cX
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem1
    adantrr
    oveq12d
    adantr
    eleqtrrd
    ex
    syl5
    ssrdv
    fssd
    @3
    @5
    @13
    @9
    @14
    @10
    @15
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
    @11
    cX
    cY
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    @12
    eqid
    #
    @11
    eqid
    #
    funcestrcsetclem5
    @3
    @12
    @11
    cE
    cU
    @4
    cwun
    cX
    cY
    funcestrcsetc.e
    wph
    cU
    cwun
    wcel
    @2
    funcestrcsetc.u
    adantr
    #
    @4
    eqid
    @2
    wph
    cX
    cU
    wcel
    #
    @0
    wph
    @26
    wi
    @1
    wph
    @0
    @26
    wph
    cB
    cU
    cX
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
    wph
    @2
    cY
    cU
    wcel
    #
    wph
    @1
    @28
    @0
    wph
    @1
    @28
    wph
    cB
    cU
    cY
    @27
    eleq2d
    biimpd
    adantld
    imp
    @23
    @24
    estrchom
    @3
    cS
    cU
    @8
    cwun
    @6
    @7
    funcestrcsetc.s
    @25
    @8
    eqid
    wph
    @0
    @6
    cU
    wcel
    @1
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cX
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem2
    adantrr
    wph
    @1
    @7
    cU
    wcel
    @0
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    cY
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem2
    adantrl
    setchom
    feq123d
    mpbird
end

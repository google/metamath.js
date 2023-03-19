include "cco.mm"
include "cfv.mm"
include "ccid.mm"
include "chom.mm"
include "eqid.mm"
include "cwun.mm"
include "wcel.mm"
include "ccat.mm"
include "estrccat.mm"
include "syl.mm"
include "setccat.mm"
include "funcestrcsetclem3.mm"
include "funcestrcsetclem4.mm"
include "cv.mm"
include "funcestrcsetclem8.mm"
include "funcestrcsetclem7.mm"
include "funcestrcsetclem9.mm"
include "isfuncd.mm"

theorem funcestrcsetc
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
  assert |- ( ph -> F ( E Func S ) G )

  proof
    wph
    va
    vb
    vc
    cB
    cC
    cE
    cE
    cco
    cfv
    #
    cE
    ccid
    cfv
    #
    vh
    vk
    cS
    cF
    cG
    cE
    chom
    cfv
    #
    cS
    ccid
    cfv
    #
    cS
    chom
    cfv
    #
    cS
    cco
    cfv
    #
    funcestrcsetc.b
    funcestrcsetc.c
    @2
    eqid
    @4
    eqid
    @1
    eqid
    @3
    eqid
    @0
    eqid
    @5
    eqid
    wph
    cU
    cwun
    wcel
    #
    cE
    ccat
    wcel
    funcestrcsetc.u
    cE
    cU
    cwun
    funcestrcsetc.e
    estrccat
    syl
    wph
    @6
    cS
    ccat
    wcel
    funcestrcsetc.u
    cS
    cU
    cwun
    funcestrcsetc.s
    setccat
    syl
    wph
    vx
    cB
    cC
    cS
    cU
    cE
    cF
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetclem3
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
    funcestrcsetclem4
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
    va
    cv
    #
    vb
    cv
    #
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    funcestrcsetclem8
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
    @7
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    funcestrcsetclem7
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
    vh
    cv
    vk
    cv
    @7
    @8
    vc
    cv
    funcestrcsetc.e
    funcestrcsetc.s
    funcestrcsetc.b
    funcestrcsetc.c
    funcestrcsetc.u
    funcestrcsetc.f
    funcestrcsetc.g
    funcestrcsetclem9
    isfuncd
end

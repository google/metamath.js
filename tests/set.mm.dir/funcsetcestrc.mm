include "cbs.mm"
include "cfv.mm"
include "cco.mm"
include "ccid.mm"
include "chom.mm"
include "eqid.mm"
include "cwun.mm"
include "wcel.mm"
include "ccat.mm"
include "setccat.mm"
include "syl.mm"
include "estrccat.mm"
include "funcsetcestrclem3.mm"
include "funcsetcestrclem4.mm"
include "cv.mm"
include "funcsetcestrclem8.mm"
include "funcsetcestrclem7.mm"
include "funcsetcestrclem9.mm"
include "isfuncd.mm"

theorem funcsetcestrc
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
  assert |- ( ph -> F ( S Func E ) G )

  proof
    wph
    va
    vb
    vc
    cC
    cE
    cbs
    cfv
    #
    cS
    cS
    cco
    cfv
    #
    cS
    ccid
    cfv
    #
    vh
    vk
    cE
    cF
    cG
    cS
    chom
    cfv
    #
    cE
    ccid
    cfv
    #
    cE
    chom
    cfv
    #
    cE
    cco
    cfv
    #
    funcsetcestrc.c
    @0
    eqid
    #
    @3
    eqid
    @5
    eqid
    @2
    eqid
    @4
    eqid
    @1
    eqid
    @6
    eqid
    wph
    cU
    cwun
    wcel
    #
    cS
    ccat
    wcel
    funcsetcestrc.u
    cS
    cU
    cwun
    funcsetcestrc.s
    setccat
    syl
    wph
    @8
    cE
    ccat
    wcel
    funcsetcestrc.u
    cE
    cU
    cwun
    funcsetcestrc.e
    estrccat
    syl
    wph
    vx
    @0
    cC
    cS
    cU
    cE
    cF
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.e
    @7
    funcsetcestrclem3
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem4
    wph
    vx
    vy
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
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrc.e
    funcsetcestrclem8
    wph
    vx
    vy
    cC
    cS
    cU
    cE
    cF
    cG
    @9
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrc.e
    funcsetcestrclem7
    wph
    vx
    vy
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
    @9
    @10
    vc
    cv
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrc.e
    funcsetcestrclem9
    isfuncd
end

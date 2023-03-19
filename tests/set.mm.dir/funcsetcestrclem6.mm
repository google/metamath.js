include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "funcsetcestrclem5.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "fvresi.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem funcsetcestrclem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  assume funcsetcestrc.s: |- S = ( SetCat ` U )
  assume funcsetcestrc.c: |- C = ( Base ` S )
  assume funcsetcestrc.f: |- ( ph -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) )
  assume funcsetcestrc.u: |- ( ph -> U e. WUni )
  assume funcsetcestrc.o: |- ( ph -> _om e. U )
  assume funcsetcestrc.g: |- ( ph -> G = ( x e. C , y e. C |-> ( _I |` ( y ^m x ) ) ) )

  disjoint C x
  disjoint X x
  disjoint ph x
  disjoint C y
  disjoint x y
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph y
  assert |- ( ( ph /\ ( X e. C /\ Y e. C ) /\ H e. ( Y ^m X ) ) -> ( ( X G Y ) ` H ) = H )

  proof
    wph
    cX
    cC
    wcel
    cY
    cC
    wcel
    wa
    #
    cH
    cY
    cX
    cmap
    co
    #
    wcel
    #
    w3a
    #
    cH
    cX
    cY
    cG
    co
    #
    cfv
    cH
    cid
    @1
    cres
    #
    cfv
    #
    cH
    @3
    cH
    @4
    @5
    wph
    @0
    @4
    @5
    wceq
    @2
    wph
    vx
    vy
    cC
    cS
    cU
    cF
    cG
    cX
    cY
    funcsetcestrc.s
    funcsetcestrc.c
    funcsetcestrc.f
    funcsetcestrc.u
    funcsetcestrc.o
    funcsetcestrc.g
    funcsetcestrclem5
    3adant3
    fveq1d
    @2
    wph
    @6
    cH
    wceq
    @0
    @1
    cH
    fvresi
    3ad2ant3
    eqtrd
end

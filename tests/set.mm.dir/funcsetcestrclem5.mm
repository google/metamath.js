include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "adantr.mm"
include "oveq12.mm"
include "ancoms.mm"
include "reseq2d.mm"
include "adantl.mm"
include "simprl.mm"
include "simprr.mm"
include "ovexd.mm"
include "resiexd.mm"
include "ovmpt2d.mm"

theorem funcsetcestrclem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
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
  assert |- ( ( ph /\ ( X e. C /\ Y e. C ) ) -> ( X G Y ) = ( _I |` ( Y ^m X ) ) )

  proof
    wph
    cX
    cC
    wcel
    #
    cY
    cC
    wcel
    #
    wa
    #
    wa
    #
    vx
    vy
    cX
    cY
    cC
    cC
    cid
    vy
    cv
    #
    vx
    cv
    #
    cmap
    co
    #
    cres
    #
    cid
    cY
    cX
    cmap
    co
    #
    cres
    #
    cG
    cvv
    wph
    cG
    vx
    vy
    cC
    cC
    @7
    cmpt2
    wceq
    @2
    funcsetcestrc.g
    adantr
    @5
    cX
    wceq
    #
    @4
    cY
    wceq
    #
    wa
    #
    @7
    @9
    wceq
    @3
    @12
    @6
    @8
    cid
    @11
    @10
    @6
    @8
    wceq
    @4
    cY
    @5
    cX
    cmap
    oveq12
    ancoms
    reseq2d
    adantl
    wph
    @0
    @1
    simprl
    wph
    @0
    @1
    simprr
    @3
    @8
    cvv
    @3
    cY
    cX
    cmap
    ovexd
    resiexd
    ovmpt2d
end

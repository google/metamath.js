include "cxp.mm"
include "wfn.mm"
include "cid.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cmpt2.mm"
include "eqid.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "id.mm"
include "resiexd.mm"
include "ax-mp.mm"
include "fnmpt2i.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem funcsetcestrclem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cX: class X
  assume funcsetcestrc.s: |- S = ( SetCat ` U )
  assume funcsetcestrc.c: |- C = ( Base ` S )
  assume funcsetcestrc.f: |- ( ph -> F = ( x e. C |-> { <. ( Base ` ndx ) , x >. } ) )
  assume funcsetcestrc.u: |- ( ph -> U e. WUni )
  assume funcsetcestrc.o: |- ( ph -> _om e. U )
  assume funcsetcestrc.g: |- ( ph -> G = ( x e. C , y e. C |-> ( _I |` ( y ^m x ) ) ) )

  disjoint C x
  disjoint ph x
  disjoint C y
  disjoint x y
  disjoint X x
  assert |- ( ph -> G Fn ( C X. C ) )

  proof
    wph
    cG
    cC
    cC
    cxp
    #
    wfn
    vx
    vy
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
    cmpt2
    #
    @0
    wfn
    vx
    vy
    cC
    cC
    @4
    @5
    @5
    eqid
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @1
    @2
    cmap
    ovex
    @6
    @3
    cvv
    @6
    id
    resiexd
    ax-mp
    fnmpt2i
    wph
    @0
    cG
    @5
    funcsetcestrc.g
    fneq1d
    mpbiri
end

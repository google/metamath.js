include "cxp.mm"
include "wfn.mm"
include "cid.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
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

theorem funcestrcsetclem4
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
  disjoint X x
  assert |- ( ph -> G Fn ( B X. B ) )

  proof
    wph
    cG
    cB
    cB
    cxp
    #
    wfn
    vx
    vy
    cB
    cB
    cid
    vy
    cv
    cbs
    cfv
    #
    vx
    cv
    cbs
    cfv
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
    cB
    cB
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
    funcestrcsetc.g
    fneq1d
    mpbiri
end

include "cxp.mm"
include "wfn.mm"
include "cid.mm"
include "cv.mm"
include "crh.mm"
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

theorem funcringcsetcALTV2lem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  assume funcringcsetcALTV2.r: |- R = ( RingCat ` U )
  assume funcringcsetcALTV2.s: |- S = ( SetCat ` U )
  assume funcringcsetcALTV2.b: |- B = ( Base ` R )
  assume funcringcsetcALTV2.c: |- C = ( Base ` S )
  assume funcringcsetcALTV2.u: |- ( ph -> U e. WUni )
  assume funcringcsetcALTV2.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetcALTV2.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

  disjoint B x
  disjoint ph x
  disjoint C x
  disjoint B y
  disjoint x y
  disjoint X x
  disjoint k x
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
    vx
    cv
    #
    vy
    cv
    #
    crh
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
    crh
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
    funcringcsetcALTV2.g
    fneq1d
    mpbiri
end

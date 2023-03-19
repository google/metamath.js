include "wcel.mm"
include "cgi.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "crio.mm"
include "gidval.mm"
include "syl5eq.mm"

theorem idrval
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  assume idrval.1: |- X = ran G
  assume idrval.2: |- U = ( GId ` G )

  disjoint G u
  disjoint G x
  disjoint u x
  disjoint X u
  disjoint X x
  assert |- ( G e. A -> U = ( iota_ u e. X A. x e. X ( ( u G x ) = x /\ ( x G u ) = x ) ) )

  proof
    cG
    cA
    wcel
    cU
    cG
    cgi
    cfv
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    @1
    wceq
    @1
    @0
    cG
    co
    @1
    wceq
    wa
    vx
    cX
    wral
    vu
    cX
    crio
    idrval.2
    vx
    vu
    cG
    cA
    cX
    idrval.1
    gidval
    syl5eq
end

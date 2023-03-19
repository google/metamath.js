include "clf.mm"
include "wcel.mm"
include "cnmf.mm"
include "cfv.mm"
include "cr.mm"
include "wa.mm"
include "ccnfn.mm"
include "cin.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wreu.mm"
include "elin.mm"
include "lnfncnbd.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "riesz4.mm"
include "sylbir.mm"

theorem riesz2
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vz: setvar z

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( ( T e. LinFn /\ ( normfn ` T ) e. RR ) -> E! y e. ~H A. x e. ~H ( T ` x ) = ( x .ih y ) )

  proof
    cT
    clf
    wcel
    #
    cT
    cnmf
    cfv
    cr
    wcel
    #
    wa
    #
    cT
    clf
    ccnfn
    cin
    wcel
    #
    vx
    cv
    #
    cT
    cfv
    @4
    vy
    cv
    csp
    co
    wceq
    vx
    chil
    wral
    vy
    chil
    wreu
    @3
    @0
    cT
    ccnfn
    wcel
    #
    wa
    @2
    cT
    clf
    ccnfn
    elin
    @0
    @5
    @1
    cT
    lnfncnbd
    pm5.32i
    bitri
    vy
    vx
    cT
    riesz4
    sylbir
end

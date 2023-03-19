include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "cmap.mm"
include "crio.mm"
include "adjval.mm"
include "wf.mm"
include "wb.mm"
include "dmadjop.mm"
include "elmapi.mm"
include "wa.mm"
include "adjsym.mm"
include "eqcom.mm"
include "2ralbii.mm"
include "syl6bb.mm"
include "syl2an.mm"
include "riotabidva.mm"
include "eqtrd.mm"

theorem adjval2
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cT: class T
  let vt: setvar t
  let vw: setvar w
  let vz: setvar z

  disjoint u x
  disjoint u y
  disjoint T u
  disjoint x y
  disjoint T x
  disjoint T y
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T e. dom adjh -> ( adjh ` T ) = ( iota_ u e. ( ~H ^m ~H ) A. x e. ~H A. y e. ~H ( ( T ` x ) .ih y ) = ( x .ih ( u ` y ) ) ) )

  proof
    cT
    cado
    cdm
    wcel
    #
    cT
    cado
    cfv
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    csp
    co
    @1
    vu
    cv
    #
    cfv
    @2
    csp
    co
    wceq
    vy
    chil
    wral
    vx
    chil
    wral
    #
    vu
    chil
    chil
    cmap
    co
    #
    crio
    @1
    cT
    cfv
    @2
    csp
    co
    #
    @1
    @2
    @3
    cfv
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    vu
    @5
    crio
    vx
    vy
    vu
    cT
    adjval
    @0
    @4
    @9
    vu
    @5
    @0
    chil
    chil
    cT
    wf
    #
    chil
    chil
    @3
    wf
    #
    @4
    @9
    wb
    @3
    @5
    wcel
    cT
    dmadjop
    @3
    chil
    chil
    elmapi
    @10
    @11
    wa
    @4
    @7
    @6
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @9
    vx
    vy
    cT
    @3
    adjsym
    @12
    @8
    vx
    vy
    chil
    chil
    @7
    @6
    eqcom
    2ralbii
    syl6bb
    syl2an
    riotabidva
    eqtrd
end

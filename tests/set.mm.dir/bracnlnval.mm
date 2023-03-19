include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "crio.mm"
include "cbr.mm"
include "ccnv.mm"
include "cnvbraval.mm"
include "wb.mm"
include "cnvbracl.mm"
include "eqeltrrd.mm"
include "wf1o.mm"
include "bra11.mm"
include "f1ocnvfvb.mm"
include "mp3an1.mm"
include "mpancom.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem bracnlnval
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint T t
  disjoint u x
  disjoint u y
  disjoint T u
  disjoint U t
  disjoint U u
  disjoint U x
  disjoint t z
  assert |- ( T e. ( LinFn i^i ContFn ) -> T = ( bra ` ( iota_ y e. ~H A. x e. ~H ( T ` x ) = ( x .ih y ) ) ) )

  proof
    cT
    clf
    ccnfn
    cin
    #
    wcel
    #
    vx
    cv
    #
    cT
    cfv
    @2
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
    crio
    #
    cbr
    cfv
    #
    cT
    @1
    @4
    cT
    wceq
    #
    cT
    cbr
    ccnv
    cfv
    #
    @3
    wceq
    #
    vx
    vy
    cT
    cnvbraval
    #
    @3
    chil
    wcel
    #
    @1
    @5
    @7
    wb
    #
    @1
    @6
    @3
    chil
    @8
    cT
    cnvbracl
    eqeltrrd
    chil
    @0
    cbr
    wf1o
    @9
    @1
    @10
    bra11
    chil
    @0
    @3
    cT
    cbr
    f1ocnvfvb
    mp3an1
    mpancom
    mpbird
    eqcomd
end

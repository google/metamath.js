include "chil.mm"
include "wf.mm"
include "cei.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "c0h.mm"
include "cdif.mm"
include "crab.mm"
include "c0v.mm"
include "wne.mm"
include "w3a.mm"
include "eigvecval.mm"
include "eleq2d.mm"
include "wa.mm"
include "wn.mm"
include "eldif.mm"
include "elch0.mm"
include "necon3bbii.mm"
include "anbi2i.mm"
include "bitri.mm"
include "anbi1i.mm"
include "fveq2.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem eleigvec
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S

  disjoint A x
  disjoint T x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T y
  disjoint T z
  disjoint T w
  assert |- ( T : ~H --> ~H -> ( A e. ( eigvec ` T ) <-> ( A e. ~H /\ A =/= 0h /\ E. x e. CC ( T ` A ) = ( x .h A ) ) ) )

  proof
    chil
    chil
    cT
    wf
    #
    cA
    cT
    cei
    cfv
    #
    wcel
    cA
    vy
    cv
    #
    cT
    cfv
    #
    vx
    cv
    #
    @2
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    vy
    chil
    c0h
    cdif
    #
    crab
    #
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    cA
    cT
    cfv
    #
    @4
    cA
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    w3a
    #
    @0
    @1
    @9
    cA
    vy
    vx
    cT
    eigvecval
    eleq2d
    cA
    @8
    wcel
    #
    @16
    wa
    @11
    @12
    wa
    #
    @16
    wa
    @10
    @17
    @18
    @19
    @16
    @18
    @11
    cA
    c0h
    wcel
    #
    wn
    #
    wa
    @19
    cA
    chil
    c0h
    eldif
    @21
    @12
    @11
    @20
    cA
    c0v
    cA
    elch0
    necon3bbii
    anbi2i
    bitri
    anbi1i
    @7
    @16
    vy
    cA
    @8
    @2
    cA
    wceq
    #
    @6
    @15
    vx
    cc
    @22
    @3
    @13
    @5
    @14
    @2
    cA
    cT
    fveq2
    @2
    cA
    @4
    csm
    oveq2
    eqeq12d
    rexbidv
    elrab
    @11
    @12
    @16
    df-3an
    3bitr4i
    syl6bb
end

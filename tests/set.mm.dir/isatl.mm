include "cal.mm"
include "wcel.mm"
include "clat.mm"
include "cdm.mm"
include "cv.mm"
include "wne.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "cbs.mm"
include "cfv.mm"
include "cglb.mm"
include "cp0.mm"
include "cple.mm"
include "catm.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "eleq12d.mm"
include "neeq2d.mm"
include "breqd.mm"
include "rexeqbidv.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "df-atl.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem isatl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let c.0: class .0.
  let vk: setvar k
  assume isatlat.b: |- B = ( Base ` K )
  assume isatlat.g: |- G = ( glb ` K )
  assume isatlat.l: |- .<_ = ( le ` K )
  assume isatlat.z: |- .0. = ( 0. ` K )
  assume isatlat.a: |- A = ( Atoms ` K )

  disjoint A y
  disjoint B x
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint k y
  disjoint A k
  disjoint k x
  disjoint B k
  disjoint K k
  disjoint .<_ k
  disjoint .0. k
  disjoint G k
  assert |- ( K e. AtLat <-> ( K e. Lat /\ B e. dom G /\ A. x e. B ( x =/= .0. -> E. y e. A y .<_ x ) ) )

  proof
    cK
    cal
    wcel
    cK
    clat
    wcel
    #
    cB
    cG
    cdm
    #
    wcel
    #
    vx
    cv
    #
    c.0
    wne
    #
    vy
    cv
    #
    @3
    c.le
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    vx
    cB
    wral
    #
    wa
    #
    wa
    @0
    @2
    @9
    w3a
    vk
    cv
    #
    cbs
    cfv
    #
    @11
    cglb
    cfv
    #
    cdm
    #
    wcel
    #
    @3
    @11
    cp0
    cfv
    #
    wne
    #
    @5
    @3
    @11
    cple
    cfv
    #
    wbr
    #
    vy
    @11
    catm
    cfv
    #
    wrex
    #
    wi
    #
    vx
    @12
    wral
    #
    wa
    @10
    vk
    cK
    clat
    cal
    @11
    cK
    wceq
    #
    @15
    @2
    @23
    @9
    @24
    @12
    cB
    @14
    @1
    @24
    @12
    cK
    cbs
    cfv
    cB
    @11
    cK
    cbs
    fveq2
    isatlat.b
    syl6eqr
    #
    @24
    @13
    cG
    @24
    @13
    cK
    cglb
    cfv
    cG
    @11
    cK
    cglb
    fveq2
    isatlat.g
    syl6eqr
    dmeqd
    eleq12d
    @24
    @22
    @8
    vx
    @12
    cB
    @25
    @24
    @17
    @4
    @21
    @7
    @24
    @16
    c.0
    @3
    @24
    @16
    cK
    cp0
    cfv
    c.0
    @11
    cK
    cp0
    fveq2
    isatlat.z
    syl6eqr
    neeq2d
    @24
    @19
    @6
    vy
    @20
    cA
    @24
    @20
    cK
    catm
    cfv
    cA
    @11
    cK
    catm
    fveq2
    isatlat.a
    syl6eqr
    @24
    @18
    c.le
    @5
    @3
    @24
    @18
    cK
    cple
    cfv
    c.le
    @11
    cK
    cple
    fveq2
    isatlat.l
    syl6eqr
    breqd
    rexeqbidv
    imbi12d
    raleqbidv
    anbi12d
    vx
    vk
    vy
    df-atl
    elrab2
    @0
    @2
    @9
    3anass
    bitr4i
end

include "copab.mm"
include "cdif.mm"
include "wn.mm"
include "wa.mm"
include "wrel.mm"
include "relopab.mm"
include "reldif.mm"
include "ax-mp.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wsbc.mm"
include "sbcan.mm"
include "sbcbii.mm"
include "opelopabsb.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcng.mm"
include "notbii.mm"
include "3bitr4ri.mm"
include "anbi12i.mm"
include "eldif.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem difopab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph z
  disjoint ph w
  disjoint ps z
  disjoint ps w
  assert |- ( { <. x , y >. | ph } \ { <. x , y >. | ps } ) = { <. x , y >. | ( ph /\ -. ps ) }

  proof
    vz
    vw
    wph
    vx
    vy
    copab
    #
    wps
    vx
    vy
    copab
    #
    cdif
    #
    wph
    wps
    wn
    #
    wa
    #
    vx
    vy
    copab
    #
    @0
    wrel
    @2
    wrel
    wph
    vx
    vy
    relopab
    @0
    @1
    reldif
    ax-mp
    @4
    vx
    vy
    relopab
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    @0
    wcel
    #
    @8
    @1
    wcel
    #
    wn
    #
    wa
    #
    @4
    vy
    @7
    wsbc
    #
    vx
    @6
    wsbc
    #
    @8
    @2
    wcel
    @8
    @5
    wcel
    wph
    vy
    @7
    wsbc
    #
    @3
    vy
    @7
    wsbc
    #
    wa
    #
    vx
    @6
    wsbc
    @15
    vx
    @6
    wsbc
    #
    @16
    vx
    @6
    wsbc
    #
    wa
    @14
    @12
    @15
    @16
    vx
    @6
    sbcan
    @13
    @17
    vx
    @6
    wph
    @3
    vy
    @7
    sbcan
    sbcbii
    @9
    @18
    @11
    @19
    wph
    vx
    vy
    @6
    @7
    opelopabsb
    wps
    vy
    @7
    wsbc
    #
    wn
    #
    vx
    @6
    wsbc
    #
    @20
    vx
    @6
    wsbc
    #
    wn
    #
    @19
    @11
    @6
    cvv
    wcel
    @22
    @24
    wb
    vz
    vex
    @20
    vx
    @6
    cvv
    sbcng
    ax-mp
    @16
    @21
    vx
    @6
    @7
    cvv
    wcel
    @16
    @21
    wb
    vw
    vex
    wps
    vy
    @7
    cvv
    sbcng
    ax-mp
    sbcbii
    @10
    @23
    wps
    vx
    vy
    @6
    @7
    opelopabsb
    notbii
    3bitr4ri
    anbi12i
    3bitr4ri
    @8
    @0
    @1
    eldif
    @4
    vx
    vy
    @6
    @7
    opelopabsb
    3bitr4i
    eqrelriiv
end

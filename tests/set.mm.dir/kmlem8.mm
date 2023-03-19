include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "cin.mm"
include "wcel.mm"
include "weu.mm"
include "wi.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wo.mm"
include "wb.mm"
include "ralnex.mm"
include "df-rex.mm"
include "rexnal.mm"
include "bitr3i.mm"
include "exsimpl.mm"
include "n0.mm"
include "sylibr.mm"
include "sylbir.mm"
include "ralimi.mm"
include "biimt.mm"
include "ralbi.mm"
include "syl.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "kmlem2.mm"
include "syl6rbbr.mm"
include "pm5.74i.mm"
include "pm4.64.mm"
include "bitri.mm"

theorem kmlem8
  let wps: wff ps
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let vv: setvar v
  let vx: setvar x
  let wph: wff ph

  disjoint u y
  disjoint u w
  disjoint u z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps v
  disjoint v w
  disjoint v z
  disjoint w x
  disjoint x z
  assert |- ( ( -. E. z e. u A. w e. z ps -> E. y A. z e. u ( z =/= (/) -> E! w w e. ( z i^i y ) ) ) <-> ( E. z e. u A. w e. z ps \/ E. y ( -. y e. u /\ A. z e. u E! w w e. ( z i^i y ) ) ) )

  proof
    wps
    vw
    vz
    cv
    #
    wral
    #
    vz
    vu
    cv
    #
    wrex
    #
    wn
    #
    @0
    c0
    wne
    #
    vw
    cv
    @0
    vy
    cv
    cin
    wcel
    vw
    weu
    #
    wi
    #
    vz
    @2
    wral
    #
    vy
    wex
    #
    wi
    @4
    vy
    vu
    wel
    wn
    #
    @6
    vz
    @2
    wral
    #
    wa
    #
    vy
    wex
    #
    wi
    @3
    @13
    wo
    @4
    @9
    @13
    @4
    @5
    vz
    @2
    wral
    #
    @9
    @13
    wb
    @4
    @1
    wn
    #
    vz
    @2
    wral
    @14
    @1
    vz
    @2
    ralnex
    @15
    @5
    vz
    @2
    @15
    vw
    vz
    wel
    #
    wps
    wn
    #
    wa
    vw
    wex
    #
    @5
    @18
    @17
    vw
    @0
    wrex
    @15
    @17
    vw
    @0
    df-rex
    wps
    vw
    @0
    rexnal
    bitr3i
    @18
    @16
    vw
    wex
    @5
    @16
    @17
    vw
    exsimpl
    vw
    @0
    n0
    sylibr
    sylbir
    ralimi
    sylbir
    @14
    @13
    @10
    @8
    wa
    #
    vy
    wex
    @9
    @14
    @12
    @19
    vy
    @14
    @11
    @8
    @10
    @14
    @6
    @7
    wb
    #
    vz
    @2
    wral
    @11
    @8
    wb
    @5
    @20
    vz
    @2
    @5
    @6
    biimt
    ralimi
    @6
    @7
    vz
    @2
    ralbi
    syl
    anbi2d
    exbidv
    @5
    vu
    vy
    vz
    vw
    kmlem2
    syl6rbbr
    syl
    pm5.74i
    @3
    @13
    pm4.64
    bitri
end

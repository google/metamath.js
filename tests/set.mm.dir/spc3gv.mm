include "wcel.mm"
include "w3a.mm"
include "wal.mm"
include "wn.mm"
include "wex.mm"
include "cv.mm"
include "wceq.mm"
include "notbid.mm"
include "spc3egv.mm"
include "exnal.mm"
include "exbii.mm"
include "bitri.mm"
include "bitr2i.mm"
include "syl6ibr.mm"
include "con4d.mm"

theorem spc3gv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  assume spc3egv.1: |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A. x A. y A. z ph -> ps ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    cC
    cX
    wcel
    w3a
    #
    wps
    wph
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    @0
    wps
    wn
    #
    wph
    wn
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    @3
    wn
    #
    @5
    @4
    vx
    vy
    vz
    cA
    cB
    cC
    cV
    cW
    cX
    vx
    cv
    cA
    wceq
    vy
    cv
    cB
    wceq
    vz
    cv
    cC
    wceq
    w3a
    wph
    wps
    spc3egv.1
    notbid
    spc3egv
    @8
    @2
    wn
    #
    vx
    wex
    @9
    @7
    @10
    vx
    @7
    @1
    wn
    #
    vy
    wex
    @10
    @6
    @11
    vy
    wph
    vz
    exnal
    exbii
    @1
    vy
    exnal
    bitri
    exbii
    @2
    vx
    exnal
    bitr2i
    syl6ibr
    con4d
end

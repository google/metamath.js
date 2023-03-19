include "cv.mm"
include "copab.mm"
include "cima.mm"
include "wcel.mm"
include "wbr.mm"
include "wrex.mm"
include "wsb.mm"
include "vex.mm"
include "elima.mm"
include "cop.mm"
include "wsbc.mm"
include "df-br.mm"
include "opelopabsb.mm"
include "sbsbc.mm"
include "sbbii.mm"
include "bitr2i.mm"
include "3bitri.mm"
include "rexbii.mm"
include "nfs1v.mm"
include "nfv.mm"
include "sbequ12r.mm"
include "cbvrex.mm"

theorem isarep1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vb: setvar b
  let vz: setvar z

  disjoint A x
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint x z
  disjoint A z
  disjoint b z
  disjoint y z
  disjoint ph z
  assert |- ( b e. ( { <. x , y >. | ph } " A ) <-> E. x e. A [ b / y ] ph )

  proof
    vb
    cv
    #
    wph
    vx
    vy
    copab
    #
    cA
    cima
    wcel
    vz
    cv
    #
    @0
    @1
    wbr
    #
    vz
    cA
    wrex
    wph
    vy
    vb
    wsb
    #
    vx
    vz
    wsb
    #
    vz
    cA
    wrex
    @4
    vx
    cA
    wrex
    vz
    @0
    @1
    cA
    vb
    vex
    elima
    @3
    @5
    vz
    cA
    @3
    @2
    @0
    cop
    @1
    wcel
    wph
    vy
    @0
    wsbc
    #
    vx
    @2
    wsbc
    #
    @5
    @2
    @0
    @1
    df-br
    wph
    vx
    vy
    @2
    @0
    opelopabsb
    @5
    @6
    vx
    vz
    wsb
    @7
    @4
    @6
    vx
    vz
    wph
    vy
    vb
    sbsbc
    sbbii
    @6
    vx
    vz
    sbsbc
    bitr2i
    3bitri
    rexbii
    @5
    @4
    vz
    vx
    cA
    @4
    vx
    vz
    nfs1v
    @4
    vz
    nfv
    @4
    vz
    vx
    sbequ12r
    cbvrex
    3bitri
end

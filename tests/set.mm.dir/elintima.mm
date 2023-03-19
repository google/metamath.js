include "cv.mm"
include "cima.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cint.mm"
include "wcel.mm"
include "wel.mm"
include "wral.mm"
include "cop.mm"
include "vex.mm"
include "elint2.mm"
include "wi.mm"
include "wal.mm"
include "elequ2.mm"
include "ralab2.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "imbi1i.mm"
include "19.23v.mm"
include "simpr.mm"
include "eleq2d.mm"
include "pm5.74i.mm"
include "wbr.mm"
include "elima.mm"
include "df-br.mm"
include "rexbii.mm"
include "bitri.mm"
include "imbi2i.mm"
include "albii.mm"
include "3bitr2i.mm"
include "cvv.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "isseti.mm"
include "19.42v.mm"
include "mpbiran2.mm"
include "alcom.mm"
include "df-ral.mm"
include "3bitr4i.mm"

theorem elintima
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint a y
  disjoint B b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint x z
  disjoint A z
  disjoint B z
  disjoint a z
  disjoint y z
  assert |- ( y e. |^| { x | E. a e. A x = ( a " B ) } <-> A. a e. A E. b e. B <. b , y >. e. a )

  proof
    vy
    cv
    #
    vx
    cv
    #
    va
    cv
    #
    cB
    cima
    #
    wceq
    #
    va
    cA
    wrex
    #
    vx
    cab
    #
    cint
    wcel
    vy
    vz
    wel
    #
    vz
    @6
    wral
    #
    vb
    cv
    #
    @0
    cop
    @2
    wcel
    #
    vb
    cB
    wrex
    #
    va
    cA
    wral
    #
    vz
    @0
    @6
    vy
    vex
    #
    elint2
    @8
    @5
    vy
    vx
    wel
    #
    wi
    #
    vx
    wal
    #
    @12
    @5
    @7
    @14
    vz
    vx
    vz
    vx
    vy
    elequ2
    ralab2
    @16
    @2
    cA
    wcel
    #
    @4
    wa
    #
    @11
    wi
    #
    va
    wal
    #
    vx
    wal
    #
    @12
    @15
    @20
    vx
    @15
    @18
    va
    wex
    #
    @14
    wi
    @18
    @14
    wi
    #
    va
    wal
    @20
    @5
    @22
    @14
    @4
    va
    cA
    df-rex
    imbi1i
    @18
    @14
    va
    19.23v
    @23
    @19
    va
    @23
    @18
    @0
    @3
    wcel
    #
    wi
    @19
    @18
    @14
    @24
    @18
    @1
    @3
    @0
    @17
    @4
    simpr
    eleq2d
    pm5.74i
    @24
    @11
    @18
    @24
    @9
    @0
    @2
    wbr
    #
    vb
    cB
    wrex
    @11
    vb
    @0
    @2
    cB
    @13
    elima
    @25
    @10
    vb
    cB
    @9
    @0
    @2
    df-br
    rexbii
    bitri
    imbi2i
    bitri
    albii
    3bitr2i
    albii
    @19
    vx
    wal
    #
    va
    wal
    @17
    @11
    wi
    #
    va
    wal
    @21
    @12
    @26
    @27
    va
    @26
    @18
    vx
    wex
    #
    @11
    wi
    @27
    @18
    @11
    vx
    19.23v
    @28
    @17
    @11
    @28
    @17
    @4
    vx
    wex
    vx
    @3
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    va
    vex
    @2
    cB
    cvv
    imaexg
    ax-mp
    isseti
    @17
    @4
    vx
    19.42v
    mpbiran2
    imbi1i
    bitri
    albii
    @19
    vx
    va
    alcom
    @11
    va
    cA
    df-ral
    3bitr4i
    bitri
    bitri
    bitri
end

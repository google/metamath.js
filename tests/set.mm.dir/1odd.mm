include "c1.mm"
include "wcel.mm"
include "cz.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "1z.mm"
include "cc0.mm"
include "0z.mm"
include "id.mm"
include "wb.mm"
include "oveq2.mm"
include "2t0e0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "1e0p1.mm"
include "a1i.mm"
include "rspcedvd.mm"
include "ax-mp.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "mpbir2an.mm"

theorem 1odd
  let vx: setvar x
  let vz: setvar z
  let cO: class O
  let vk: setvar k
  assume oddinmgm.e: |- O = { z e. ZZ | E. x e. ZZ z = ( ( 2 x. x ) + 1 ) }

  disjoint x z
  disjoint k x
  assert |- 1 e. O

  proof
    c1
    cO
    wcel
    c1
    cz
    wcel
    c1
    c2
    vx
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    1z
    cc0
    cz
    wcel
    #
    @4
    0z
    @5
    @3
    c1
    cc0
    c1
    caddc
    co
    #
    wceq
    #
    vx
    cc0
    cz
    @5
    id
    @0
    cc0
    wceq
    #
    @3
    @7
    wb
    @5
    @8
    @2
    @6
    c1
    @8
    @1
    cc0
    c1
    caddc
    @8
    @1
    c2
    cc0
    cmul
    co
    cc0
    @0
    cc0
    c2
    cmul
    oveq2
    2t0e0
    syl6eq
    oveq1d
    eqeq2d
    adantl
    @7
    @5
    1e0p1
    a1i
    rspcedvd
    ax-mp
    vz
    cv
    #
    @2
    wceq
    #
    vx
    cz
    wrex
    @4
    vz
    c1
    cz
    cO
    @9
    c1
    wceq
    @10
    @3
    vx
    cz
    @9
    c1
    @2
    eqeq1
    rexbidv
    oddinmgm.e
    elrab2
    mpbir2an
end

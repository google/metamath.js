include "c1.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wnel.mm"
include "cmgm.mm"
include "1odd.mm"
include "c2.mm"
include "2nodd.mm"
include "wceq.mm"
include "wb.mm"
include "1p1e2.mm"
include "neleq1.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "oddibas.mm"
include "oddiadd.mm"
include "isnmgm.mm"
include "mp3an.mm"

theorem oddinmgm
  let vx: setvar x
  let vz: setvar z
  let cM: class M
  let cO: class O
  let vk: setvar k
  assume oddinmgm.e: |- O = { z e. ZZ | E. x e. ZZ z = ( ( 2 x. x ) + 1 ) }
  assume oddinmgm.r: |- M = ( CCfld |`s O )

  disjoint x z
  disjoint k x
  assert |- M e/ Mgm

  proof
    c1
    cO
    wcel
    #
    @0
    c1
    c1
    caddc
    co
    #
    cO
    wnel
    #
    cM
    cmgm
    wnel
    vx
    vz
    cO
    oddinmgm.e
    1odd
    #
    @3
    @2
    c2
    cO
    wnel
    #
    vx
    vz
    cO
    oddinmgm.e
    2nodd
    @1
    c2
    wceq
    @2
    @4
    wb
    1p1e2
    @1
    c2
    cO
    neleq1
    ax-mp
    mpbir
    cO
    cM
    c1
    c1
    caddc
    vx
    vz
    cM
    cO
    oddinmgm.e
    oddinmgm.r
    oddibas
    vx
    vz
    cM
    cO
    oddinmgm.e
    oddinmgm.r
    oddiadd
    isnmgm
    mp3an
end

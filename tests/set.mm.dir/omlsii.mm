include "cv.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "sheli.mm"
include "pjhthlem2.mm"
include "wa.mm"
include "wi.mm"
include "c0v.mm"
include "cif.mm"
include "eqeq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "imbi1d.mm"
include "oveq2.mm"
include "chshii.mm"
include "csh.mm"
include "sh0.mm"
include "ax-mp.mm"
include "elimel.mm"
include "cch.mm"
include "ch0.mm"
include "shocsh.mm"
include "omlsilem.mm"
include "dedth3h.mm"
include "3expia.mm"
include "rexlimdv.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem omlsii
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume omlsi.1: |- A e. CH
  assume omlsi.2: |- B e. SH
  assume omlsi.3: |- A C_ B
  assume omlsi.4: |- ( B i^i ( _|_ ` A ) ) = 0H


  assert |- A = B

  proof
    cA
    cB
    omlsi.3
    vx
    cB
    cA
    vx
    cv
    #
    cB
    wcel
    #
    @0
    vy
    cv
    #
    vz
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    cA
    cort
    cfv
    #
    wrex
    #
    vy
    cA
    wrex
    @0
    cA
    wcel
    #
    @1
    vy
    vz
    @0
    cA
    omlsi.1
    @0
    cB
    omlsi.2
    sheli
    pjhthlem2
    @1
    @7
    @8
    vy
    cA
    @1
    @2
    cA
    wcel
    #
    wa
    @5
    @8
    vz
    @6
    @1
    @9
    @3
    @6
    wcel
    #
    @5
    @8
    wi
    #
    @1
    @9
    @10
    @11
    @1
    @0
    c0v
    cif
    #
    @4
    wceq
    #
    @12
    cA
    wcel
    #
    wi
    @12
    @9
    @2
    c0v
    cif
    #
    @3
    cva
    co
    #
    wceq
    #
    @14
    wi
    @12
    @15
    @10
    @3
    c0v
    cif
    #
    cva
    co
    #
    wceq
    #
    @14
    wi
    @0
    @2
    @3
    c0v
    c0v
    c0v
    @0
    @12
    wceq
    @5
    @13
    @8
    @14
    @0
    @12
    @4
    eqeq1
    @0
    @12
    cA
    eleq1
    imbi12d
    @2
    @15
    wceq
    #
    @13
    @17
    @14
    @21
    @4
    @16
    @12
    @2
    @15
    @3
    cva
    oveq1
    eqeq2d
    imbi1d
    @3
    @18
    wceq
    #
    @17
    @20
    @14
    @22
    @16
    @19
    @12
    @3
    @18
    @15
    cva
    oveq2
    eqeq2d
    imbi1d
    @12
    @15
    @18
    cA
    cB
    cA
    omlsi.1
    chshii
    #
    omlsi.2
    omlsi.3
    omlsi.4
    @0
    c0v
    cB
    cB
    csh
    wcel
    c0v
    cB
    wcel
    omlsi.2
    cB
    sh0
    ax-mp
    elimel
    @2
    c0v
    cA
    cA
    cch
    wcel
    c0v
    cA
    wcel
    omlsi.1
    cA
    ch0
    ax-mp
    elimel
    @3
    c0v
    @6
    @6
    csh
    wcel
    #
    c0v
    @6
    wcel
    cA
    csh
    wcel
    @24
    @23
    cA
    shocsh
    ax-mp
    @6
    sh0
    ax-mp
    elimel
    omlsilem
    dedth3h
    3expia
    rexlimdv
    rexlimdva
    mpd
    ssriv
    eqssi
end

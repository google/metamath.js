include "cmnf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "wi.mm"
include "cxr.mm"
include "wcel.mm"
include "cpnf.mm"
include "wceq.mm"
include "w3o.mm"
include "elxr.mm"
include "reltre.mm"
include "rspec.mm"
include "a1d.mm"
include "cc0.mm"
include "0red.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "0ltpnf.mm"
include "breq2.mm"
include "mpbiri.mm"
include "rspcedvd.mm"
include "mnfxr.mm"
include "nltmnf.mm"
include "pm2.21d.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "rgen.mm"

theorem reltxrnmnf
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- A. x e. RR* ( -oo < x -> E. y e. RR y < x )

  proof
    cmnf
    vx
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    @0
    clt
    wbr
    #
    vy
    cr
    wrex
    #
    wi
    #
    vx
    cxr
    @0
    cxr
    wcel
    @0
    cr
    wcel
    #
    @0
    cpnf
    wceq
    #
    @0
    cmnf
    wceq
    #
    w3o
    @5
    @0
    elxr
    @6
    @5
    @7
    @8
    @6
    @4
    @1
    @4
    vx
    cr
    vx
    vy
    reltre
    rspec
    a1d
    @7
    @4
    @1
    @7
    @3
    cc0
    @0
    clt
    wbr
    #
    vy
    cc0
    cr
    @7
    0red
    @2
    cc0
    wceq
    @3
    @9
    wb
    @7
    @2
    cc0
    @0
    clt
    breq1
    adantl
    @7
    @9
    cc0
    cpnf
    clt
    wbr
    0ltpnf
    @0
    cpnf
    cc0
    clt
    breq2
    mpbiri
    rspcedvd
    a1d
    @8
    @1
    cmnf
    cmnf
    clt
    wbr
    #
    @4
    @0
    cmnf
    cmnf
    clt
    breq2
    cmnf
    cxr
    wcel
    #
    @10
    @4
    wi
    mnfxr
    @11
    @10
    @4
    cmnf
    nltmnf
    pm2.21d
    ax-mp
    syl6bi
    3jaoi
    sylbi
    rgen
end

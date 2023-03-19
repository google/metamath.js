include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "cr.mm"
include "cinf.mm"
include "cc0.mm"
include "wceq.mm"
include "rpltrp.mm"
include "wor.mm"
include "ltso.mm"
include "a1i.mm"
include "0red.mm"
include "wcel.mm"
include "wn.mm"
include "rpre.mm"
include "rpge0.mm"
include "lensymd.mm"
include "adantl.mm"
include "wa.mm"
include "wi.mm"
include "elrp.mm"
include "weq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sylbir.mm"
include "impcom.mm"
include "eqinfd.mm"
include "ax-mp.mm"

theorem infmrp1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- inf ( RR+ , RR , < ) = 0

  proof
    vy
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vy
    crp
    wrex
    #
    vx
    crp
    wral
    #
    crp
    cr
    clt
    cinf
    cc0
    wceq
    vx
    vy
    rpltrp
    @4
    vz
    vy
    cr
    crp
    cc0
    clt
    cr
    clt
    wor
    @4
    ltso
    a1i
    @4
    0red
    vz
    cv
    #
    crp
    wcel
    #
    @5
    cc0
    clt
    wbr
    wn
    @4
    @6
    cc0
    @5
    @6
    0red
    @5
    rpre
    @5
    rpge0
    lensymd
    adantl
    @5
    cr
    wcel
    cc0
    @5
    clt
    wbr
    wa
    #
    @4
    @0
    @5
    clt
    wbr
    #
    vy
    crp
    wrex
    #
    @7
    @6
    @4
    @9
    wi
    @5
    elrp
    @3
    @9
    vx
    @5
    crp
    vx
    vz
    weq
    @2
    @8
    vy
    crp
    @1
    @5
    @0
    clt
    breq2
    rexbidv
    rspcv
    sylbir
    impcom
    eqinfd
    ax-mp
end

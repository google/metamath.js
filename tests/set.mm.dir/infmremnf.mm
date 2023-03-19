include "cmnf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wrex.mm"
include "wi.mm"
include "cxr.mm"
include "wral.mm"
include "cinf.mm"
include "wceq.mm"
include "reltxrnmnf.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "wcel.mm"
include "mnfxr.mm"
include "wn.mm"
include "rexr.mm"
include "nltmnf.mm"
include "syl.mm"
include "adantl.mm"
include "wa.mm"
include "weq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "imp.mm"
include "impcom.mm"
include "eqinfd.mm"
include "ax-mp.mm"

theorem infmremnf
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- inf ( RR , RR* , < ) = -oo

  proof
    cmnf
    vx
    cv
    #
    clt
    wbr
    #
    vz
    cv
    #
    @0
    clt
    wbr
    #
    vz
    cr
    wrex
    #
    wi
    #
    vx
    cxr
    wral
    #
    cr
    cxr
    clt
    cinf
    cmnf
    wceq
    vx
    vz
    reltxrnmnf
    @6
    vy
    vz
    cxr
    cr
    cmnf
    clt
    cxr
    clt
    wor
    @6
    xrltso
    a1i
    cmnf
    cxr
    wcel
    @6
    mnfxr
    a1i
    vy
    cv
    #
    cr
    wcel
    #
    @7
    cmnf
    clt
    wbr
    wn
    #
    @6
    @8
    @7
    cxr
    wcel
    #
    @9
    @7
    rexr
    @7
    nltmnf
    syl
    adantl
    @10
    cmnf
    @7
    clt
    wbr
    #
    wa
    @6
    @2
    @7
    clt
    wbr
    #
    vz
    cr
    wrex
    #
    @10
    @11
    @6
    @13
    wi
    @10
    @6
    @11
    @13
    @5
    @11
    @13
    wi
    vx
    @7
    cxr
    vx
    vy
    weq
    #
    @1
    @11
    @4
    @13
    @0
    @7
    cmnf
    clt
    breq2
    @14
    @3
    @12
    vz
    cr
    @0
    @7
    @2
    clt
    breq2
    rexbidv
    imbi12d
    rspcv
    com23
    imp
    impcom
    eqinfd
    ax-mp
end

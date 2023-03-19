include "c0.mm"
include "cmee.mm"
include "cfv.mm"
include "cv.mm"
include "cpr.mm"
include "cglb.mm"
include "wbr.mm"
include "coprab.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "0ex.mm"
include "eqid.mm"
include "meetfval.mm"
include "ax-mp.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-oprab.mm"
include "br0.mm"
include "cpw.mm"
include "cple.mm"
include "wral.mm"
include "wi.mm"
include "crio.mm"
include "cmpt.mm"
include "wreu.mm"
include "cres.mm"
include "base0.mm"
include "biid.mm"
include "id.mm"
include "glbfval.mm"
include "wrex.mm"
include "rex0.mm"
include "reurex.mm"
include "mto.mm"
include "abf.mm"
include "reseq2i.mm"
include "res0.mm"
include "eqtri.mm"
include "breqi.mm"
include "mtbir.mm"
include "intnan.mm"
include "nex.mm"

theorem meet0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( meet ` (/) ) = (/)

  proof
    c0
    cmee
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    vz
    cv
    #
    c0
    cglb
    cfv
    #
    wbr
    #
    vx
    vy
    vz
    coprab
    #
    c0
    c0
    cvv
    wcel
    #
    @0
    @7
    wceq
    0ex
    vx
    vy
    vz
    @5
    c0
    @0
    cvv
    @5
    eqid
    #
    @0
    eqid
    meetfval
    ax-mp
    @7
    vw
    cv
    #
    @1
    @2
    cop
    @4
    cop
    wceq
    #
    @6
    wa
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
    vw
    cab
    c0
    @6
    vx
    vy
    vz
    vw
    df-oprab
    @15
    vw
    @14
    vx
    @13
    vy
    @12
    vz
    @6
    @11
    @6
    @3
    @4
    c0
    wbr
    @3
    @4
    br0
    @3
    @4
    @5
    c0
    @5
    vx
    c0
    cpw
    @2
    @4
    c0
    cple
    cfv
    #
    wbr
    vz
    @1
    wral
    @10
    @4
    @16
    wbr
    vz
    @1
    wral
    @10
    @2
    @16
    wbr
    wi
    vw
    c0
    wral
    wa
    #
    vy
    c0
    crio
    cmpt
    #
    @17
    vy
    c0
    wreu
    #
    vx
    cab
    #
    cres
    #
    c0
    @8
    @5
    @21
    wceq
    0ex
    @8
    @17
    vy
    vz
    vw
    c0
    @5
    c0
    @16
    cvv
    vx
    base0
    @16
    eqid
    @9
    @17
    biid
    @8
    id
    glbfval
    ax-mp
    @21
    @18
    c0
    cres
    c0
    @20
    c0
    @18
    @19
    vx
    @19
    @17
    vy
    c0
    wrex
    @17
    vy
    rex0
    @17
    vy
    c0
    reurex
    mto
    abf
    reseq2i
    @18
    res0
    eqtri
    eqtri
    breqi
    mtbir
    intnan
    nex
    nex
    nex
    abf
    eqtri
    eqtri
end

include "con0.mm"
include "com.mm"
include "cv.mm"
include "wss.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cab.mm"
include "cep.mm"
include "cale.mm"
include "wiso.mm"
include "wf1o.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "wf1.mm"
include "wfo.mm"
include "wf.mm"
include "wi.mm"
include "wfn.mm"
include "crn.mm"
include "alephfnon.mm"
include "wcel.mm"
include "isinfcard.mm"
include "bicomi.mm"
include "abbi2i.mm"
include "df-fo.mm"
include "mpbir2an.mm"
include "fof.mm"
include "ax-mp.mm"
include "aleph11.mm"
include "biimpd.mm"
include "rgen2a.mm"
include "dff13.mm"
include "df-f1o.mm"
include "alephord2.mm"
include "epel.mm"
include "fvex.mm"
include "epelc.mm"
include "3bitr4g.mm"
include "df-isom.mm"

theorem alephiso
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- aleph Isom _E , _E ( On , { x | ( _om C_ x /\ ( card ` x ) = x ) } )

  proof
    con0
    com
    vx
    cv
    #
    wss
    @0
    ccrd
    cfv
    @0
    wceq
    wa
    #
    vx
    cab
    #
    cep
    cep
    cale
    wiso
    con0
    @2
    cale
    wf1o
    #
    vy
    cv
    #
    vz
    cv
    #
    cep
    wbr
    #
    @4
    cale
    cfv
    #
    @5
    cale
    cfv
    #
    cep
    wbr
    #
    wb
    #
    vz
    con0
    wral
    vy
    con0
    wral
    @3
    con0
    @2
    cale
    wf1
    #
    con0
    @2
    cale
    wfo
    #
    @11
    con0
    @2
    cale
    wf
    #
    @7
    @8
    wceq
    #
    @4
    @5
    wceq
    #
    wi
    #
    vz
    con0
    wral
    vy
    con0
    wral
    @12
    @13
    @12
    cale
    con0
    wfn
    cale
    crn
    #
    @2
    wceq
    alephfnon
    @1
    vx
    @17
    @1
    @0
    @17
    wcel
    @0
    isinfcard
    bicomi
    abbi2i
    con0
    @2
    cale
    df-fo
    mpbir2an
    #
    con0
    @2
    cale
    fof
    ax-mp
    @16
    vy
    vz
    con0
    @4
    con0
    wcel
    @5
    con0
    wcel
    wa
    #
    @14
    @15
    @4
    @5
    aleph11
    biimpd
    rgen2a
    vy
    vz
    con0
    @2
    cale
    dff13
    mpbir2an
    @18
    con0
    @2
    cale
    df-f1o
    mpbir2an
    @10
    vy
    vz
    con0
    @19
    @4
    @5
    wcel
    @7
    @8
    wcel
    @6
    @9
    @4
    @5
    alephord2
    vy
    vz
    epel
    @7
    @8
    @5
    cale
    fvex
    epelc
    3bitr4g
    rgen2a
    vy
    vz
    con0
    @2
    cep
    cep
    cale
    df-isom
    mpbir2an
end

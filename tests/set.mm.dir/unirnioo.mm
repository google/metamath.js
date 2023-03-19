include "cr.mm"
include "cioo.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wss.mm"
include "cmnf.mm"
include "cpnf.mm"
include "co.mm"
include "ioomax.mm"
include "cxr.mm"
include "cxp.mm"
include "wfn.mm"
include "cpw.mm"
include "wf.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "fnovrn.mm"
include "mp3an.mm"
include "eqeltrri.mm"
include "elssuni.mm"
include "frn.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "eqssi.mm"

theorem unirnioo
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- RR = U. ran (,)

  proof
    cr
    cioo
    crn
    #
    cuni
    #
    cr
    @0
    wcel
    cr
    @1
    wss
    cmnf
    cpnf
    cioo
    co
    #
    cr
    @0
    ioomax
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    cmnf
    cxr
    wcel
    cpnf
    cxr
    wcel
    @2
    @0
    wcel
    @3
    cr
    cpw
    #
    cioo
    wf
    #
    @4
    ioof
    @3
    @5
    cioo
    ffn
    ax-mp
    mnfxr
    pnfxr
    cxr
    cxr
    cmnf
    cpnf
    cioo
    fnovrn
    mp3an
    eqeltrri
    cr
    @0
    elssuni
    ax-mp
    @0
    @5
    wss
    #
    @1
    cr
    wss
    @6
    @7
    ioof
    @3
    @5
    cioo
    frn
    ax-mp
    @0
    cr
    sspwuni
    mpbi
    eqssi
end

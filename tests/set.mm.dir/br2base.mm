include "cbrsiga.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "cr.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "wceq.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "brsigasspwrn.mm"
include "sseli.mm"
include "elpwid.mm"
include "xpss12.mm"
include "syl2an.mm"
include "vex.mm"
include "xpex.mm"
include "elpw.mm"
include "sylibr.mm"
include "rgen2a.mm"
include "eqid.mm"
include "rnmpt2ss.mm"
include "ax-mp.mm"
include "wb.mm"
include "wrex.mm"
include "unibrsiga.mm"
include "csiga.mm"
include "cfv.mm"
include "brsigarn.mm"
include "elrnsiga.mm"
include "unielsiga.mm"
include "mp2b.mm"
include "eqeltrri.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "mp3an.mm"
include "elrnmpt2.mm"
include "mpbir.mm"
include "elpwuni.mm"
include "mpbi.mm"

theorem br2base
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- U. ran ( x e. BrSiga , y e. BrSiga |-> ( x X. y ) ) = ( RR X. RR )

  proof
    vx
    vy
    cbrsiga
    cbrsiga
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    cr
    cr
    cxp
    #
    cpw
    #
    wss
    #
    @4
    cuni
    @5
    wceq
    #
    @2
    @6
    wcel
    #
    vy
    cbrsiga
    wral
    vx
    cbrsiga
    wral
    @7
    @9
    vx
    vy
    cbrsiga
    @0
    cbrsiga
    wcel
    #
    @1
    cbrsiga
    wcel
    #
    wa
    @2
    @5
    wss
    #
    @9
    @10
    @0
    cr
    wss
    @1
    cr
    wss
    @12
    @11
    @10
    @0
    cr
    cbrsiga
    cr
    cpw
    #
    @0
    brsigasspwrn
    sseli
    elpwid
    @11
    @1
    cr
    cbrsiga
    @13
    @1
    brsigasspwrn
    sseli
    elpwid
    @0
    cr
    @1
    cr
    xpss12
    syl2an
    @2
    @5
    @0
    @1
    vx
    vex
    vy
    vex
    xpex
    #
    elpw
    sylibr
    rgen2a
    vx
    vy
    cbrsiga
    cbrsiga
    @2
    @6
    @3
    @3
    eqid
    #
    rnmpt2ss
    ax-mp
    @5
    @4
    wcel
    #
    @7
    @8
    wb
    @16
    @5
    @2
    wceq
    #
    vy
    cbrsiga
    wrex
    vx
    cbrsiga
    wrex
    #
    cr
    cbrsiga
    wcel
    #
    @19
    @5
    @5
    wceq
    #
    @18
    cbrsiga
    cuni
    #
    cr
    cbrsiga
    unibrsiga
    cbrsiga
    cr
    csiga
    cfv
    wcel
    cbrsiga
    csiga
    crn
    cuni
    wcel
    @21
    cbrsiga
    wcel
    brsigarn
    cbrsiga
    cr
    elrnsiga
    cbrsiga
    unielsiga
    mp2b
    eqeltrri
    #
    @22
    @5
    eqid
    @17
    @20
    @5
    cr
    @1
    cxp
    #
    wceq
    vx
    vy
    cr
    cr
    cbrsiga
    cbrsiga
    @0
    cr
    wceq
    @2
    @23
    @5
    @0
    cr
    @1
    xpeq1
    eqeq2d
    @1
    cr
    wceq
    @23
    @5
    @5
    @1
    cr
    cr
    xpeq2
    eqeq2d
    rspc2ev
    mp3an
    vx
    vy
    cbrsiga
    cbrsiga
    @2
    @5
    @3
    @15
    @14
    elrnmpt2
    mpbir
    @4
    @5
    elpwuni
    ax-mp
    mpbi
end

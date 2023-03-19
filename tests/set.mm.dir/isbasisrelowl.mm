include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "ctb.mm"
include "cico.mm"
include "cr.mm"
include "cxp.mm"
include "cima.mm"
include "cle.mm"
include "clt.mm"
include "df-ico.mm"
include "ixxex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "icoreclin.mm"
include "rgen2a.mm"
include "fiinbas.mm"
include "mp2an.mm"

theorem isbasisrelowl
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume isbasisrelowl.1: |- I = ( [,) " ( RR X. RR ) )


  assert |- I e. TopBases

  proof
    cI
    cvv
    wcel
    vx
    cv
    vy
    cv
    cin
    cI
    wcel
    #
    vy
    cI
    wral
    vx
    cI
    wral
    cI
    ctb
    wcel
    cI
    cico
    cr
    cr
    cxp
    #
    cima
    #
    cvv
    isbasisrelowl.1
    cico
    cvv
    wcel
    @2
    cvv
    wcel
    vx
    vy
    vz
    cle
    clt
    cico
    vx
    vy
    vz
    df-ico
    ixxex
    cico
    @1
    cvv
    imaexg
    ax-mp
    eqeltri
    @0
    vx
    vy
    cI
    vx
    vy
    cI
    isbasisrelowl.1
    icoreclin
    rgen2a
    vx
    vy
    cI
    cvv
    fiinbas
    mp2an
end

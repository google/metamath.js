include "crefld.mm"
include "ctos.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wor.mm"
include "cid.mm"
include "cres.mm"
include "cle.mm"
include "wss.mm"
include "ltso.mm"
include "cv.mm"
include "wbr.mm"
include "idref.mm"
include "leid.mm"
include "mprgbir.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "df-refld.mm"
include "ovex.mm"
include "eqeltri.mm"
include "rebase.mm"
include "rele2.mm"
include "relt.mm"
include "tosso.mm"
include "ax-mp.mm"
include "mpbir2an.mm"

theorem retos
  let vx: setvar x


  assert |- RRfld e. Toset

  proof
    crefld
    ctos
    wcel
    #
    cr
    clt
    wor
    #
    cid
    cr
    cres
    cle
    wss
    #
    ltso
    @2
    vx
    cv
    #
    @3
    cle
    wbr
    vx
    cr
    vx
    cr
    cle
    idref
    @3
    leid
    mprgbir
    crefld
    cvv
    wcel
    @0
    @1
    @2
    wa
    wb
    crefld
    ccnfld
    cr
    cress
    co
    cvv
    df-refld
    ccnfld
    cr
    cress
    ovex
    eqeltri
    cr
    clt
    crefld
    cle
    cvv
    rebase
    rele2
    relt
    tosso
    ax-mp
    mpbir2an
end

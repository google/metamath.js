include "cpinfty.mm"
include "cc0.mm"
include "cinftyexpi.mm"
include "cfv.mm"
include "cccbar.mm"
include "df-bj-pinfty.mm"
include "cccinfty.mm"
include "bj-ccinftyssccbar.mm"
include "cpi.mm"
include "cneg.mm"
include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "0re.mm"
include "pipos.mm"
include "pire.mm"
include "ltnegi.mm"
include "mpbi.mm"
include "neg0.mm"
include "breqtri.mm"
include "ltleii.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "renegcli.mm"
include "rexri.mm"
include "elioc2.mm"
include "mp2an.mm"
include "mpbir3an.mm"
include "bj-elccinfty.mm"
include "ax-mp.mm"
include "sselii.mm"
include "eqeltri.mm"

theorem bj-pinftyccb



  assert |- pinfty e. CCbar

  proof
    cpinfty
    cc0
    cinftyexpi
    cfv
    #
    cccbar
    df-bj-pinfty
    cccinfty
    cccbar
    @0
    bj-ccinftyssccbar
    cc0
    cpi
    cneg
    #
    cpi
    cioc
    co
    wcel
    #
    @0
    cccinfty
    wcel
    @2
    cc0
    cr
    wcel
    #
    @1
    cc0
    clt
    wbr
    #
    cc0
    cpi
    cle
    wbr
    #
    0re
    @1
    cc0
    cneg
    #
    cc0
    clt
    cc0
    cpi
    clt
    wbr
    @1
    @6
    clt
    wbr
    pipos
    cc0
    cpi
    0re
    pire
    ltnegi
    mpbi
    neg0
    breqtri
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    @1
    cxr
    wcel
    cpi
    cr
    wcel
    @2
    @3
    @4
    @5
    w3a
    wb
    @1
    cpi
    pire
    renegcli
    rexri
    pire
    @1
    cpi
    cc0
    elioc2
    mp2an
    mpbir3an
    cc0
    bj-elccinfty
    ax-mp
    sselii
    eqeltri
end

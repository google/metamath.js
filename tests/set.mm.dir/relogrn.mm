include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "cpi.mm"
include "cneg.mm"
include "cim.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "clog.mm"
include "crn.mm"
include "recn.mm"
include "cc0.mm"
include "pipos.mm"
include "wb.mm"
include "pire.mm"
include "lt0neg2.mm"
include "ax-mp.mm"
include "mpbi.mm"
include "reim0.mm"
include "syl5breqr.mm"
include "0re.mm"
include "ltleii.mm"
include "syl6eqbr.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"

theorem relogrn
  let cA: class A


  assert |- ( A e. RR -> A e. ran log )

  proof
    cA
    cr
    wcel
    #
    cA
    cc
    wcel
    cpi
    cneg
    #
    cA
    cim
    cfv
    #
    clt
    wbr
    @2
    cpi
    cle
    wbr
    cA
    clog
    crn
    wcel
    cA
    recn
    @0
    @1
    cc0
    @2
    clt
    cc0
    cpi
    clt
    wbr
    #
    @1
    cc0
    clt
    wbr
    #
    pipos
    cpi
    cr
    wcel
    @3
    @4
    wb
    pire
    cpi
    lt0neg2
    ax-mp
    mpbi
    cA
    reim0
    #
    syl5breqr
    @0
    @2
    cc0
    cpi
    cle
    @5
    cc0
    cpi
    0re
    pire
    pipos
    ltleii
    syl6eqbr
    cA
    ellogrn
    syl3anbrc
end

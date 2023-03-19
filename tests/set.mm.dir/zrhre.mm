include "crefld.mm"
include "czrh.mm"
include "cfv.mm"
include "cz.mm"
include "cv.mm"
include "c1.mm"
include "cmg.mm"
include "co.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "cdr.mm"
include "wcel.mm"
include "crg.mm"
include "wceq.mm"
include "cr.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "resubdrg.mm"
include "simpri.mm"
include "drngring.mm"
include "eqid.mm"
include "re1r.mm"
include "zrhval2.mm"
include "mp2b.mm"
include "cmul.mm"
include "1re.mm"
include "remulg.mm"
include "mpan2.mm"
include "zre.mm"
include "ax-1rid.mm"
include "syl.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "mptresid.mm"
include "3eqtri.mm"

theorem zrhre
  let vn: setvar n


  assert |- ( ZRHom ` RRfld ) = ( _I |` ZZ )

  proof
    crefld
    czrh
    cfv
    #
    vn
    cz
    vn
    cv
    #
    c1
    crefld
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    vn
    cz
    @1
    cmpt
    cid
    cz
    cres
    crefld
    cdr
    wcel
    #
    crefld
    crg
    wcel
    @0
    @4
    wceq
    cr
    ccnfld
    csubrg
    cfv
    wcel
    @5
    resubdrg
    simpri
    crefld
    drngring
    crefld
    @2
    c1
    vn
    @0
    @0
    eqid
    @2
    eqid
    re1r
    zrhval2
    mp2b
    vn
    cz
    @3
    @1
    @1
    cz
    wcel
    #
    @3
    @1
    c1
    cmul
    co
    #
    @1
    @6
    c1
    cr
    wcel
    @3
    @7
    wceq
    1re
    c1
    @1
    remulg
    mpan2
    @6
    @1
    cr
    wcel
    @7
    @1
    wceq
    @1
    zre
    @1
    ax-1rid
    syl
    eqtrd
    mpteq2ia
    vn
    cz
    mptresid
    3eqtri
end

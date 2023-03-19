include "ccnfld.mm"
include "cdr.mm"
include "wcel.mm"
include "cz.mm"
include "cvv.mm"
include "cmgp.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "zring.mm"
include "wceq.mm"
include "cndrng.mm"
include "zex.mm"
include "df-zring.mm"
include "eqid.mm"
include "mgpress.mm"
include "mp2an.mm"

theorem zringmpg



  assert |- ( ( mulGrp ` CCfld ) |`s ZZ ) = ( mulGrp ` ZZring )

  proof
    ccnfld
    cdr
    wcel
    cz
    cvv
    wcel
    ccnfld
    cmgp
    cfv
    #
    cz
    cress
    co
    zring
    cmgp
    cfv
    wceq
    cndrng
    zex
    cz
    ccnfld
    zring
    @0
    cdr
    cvv
    df-zring
    @0
    eqid
    mgpress
    mp2an
end

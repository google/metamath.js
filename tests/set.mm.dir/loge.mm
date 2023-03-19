include "ceu.mm"
include "clog.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "ce.mm"
include "df-e.mm"
include "eqcomi.mm"
include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "wb.mm"
include "epr.mm"
include "1re.mm"
include "relogeftb.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem loge



  assert |- ( log ` _e ) = 1

  proof
    ceu
    clog
    cfv
    c1
    wceq
    #
    c1
    ce
    cfv
    #
    ceu
    wceq
    #
    ceu
    @1
    df-e
    eqcomi
    ceu
    crp
    wcel
    c1
    cr
    wcel
    @0
    @2
    wb
    epr
    1re
    ceu
    c1
    relogeftb
    mp2an
    mpbir
end

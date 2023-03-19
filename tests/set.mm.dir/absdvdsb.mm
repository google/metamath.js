include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "cneg.mm"
include "wi.mm"
include "breq1.mm"
include "bicomd.mm"
include "a1i.mm"
include "negdvdsb.mm"
include "sylan9bb.mm"
include "ex.mm"
include "wo.mm"
include "zre.mm"
include "absord.mm"
include "adantr.mm"
include "mpjaod.mm"

theorem absdvdsb
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> ( abs ` M ) || N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cabs
    cfv
    #
    cM
    wceq
    #
    cM
    cN
    cdvds
    wbr
    #
    @3
    cN
    cdvds
    wbr
    #
    wb
    #
    @3
    cM
    cneg
    #
    wceq
    #
    @4
    @7
    wi
    @2
    @4
    @6
    @5
    @3
    cM
    cN
    cdvds
    breq1
    bicomd
    a1i
    @2
    @9
    @7
    @2
    @5
    @8
    cN
    cdvds
    wbr
    #
    @9
    @6
    cM
    cN
    negdvdsb
    @9
    @6
    @10
    @3
    @8
    cN
    cdvds
    breq1
    bicomd
    sylan9bb
    ex
    @0
    @4
    @9
    wo
    @1
    @0
    cM
    cM
    zre
    absord
    adantr
    mpjaod
end

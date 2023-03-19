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
include "breq2.mm"
include "bicomd.mm"
include "a1i.mm"
include "dvdsnegb.mm"
include "sylan9bb.mm"
include "ex.mm"
include "wo.mm"
include "zre.mm"
include "absord.mm"
include "adantl.mm"
include "mpjaod.mm"

theorem dvdsabsb
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> M || ( abs ` N ) ) )

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
    cN
    cabs
    cfv
    #
    cN
    wceq
    #
    cM
    cN
    cdvds
    wbr
    #
    cM
    @3
    cdvds
    wbr
    #
    wb
    #
    @3
    cN
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
    cN
    cM
    cdvds
    breq2
    bicomd
    a1i
    @2
    @9
    @7
    @2
    @5
    cM
    @8
    cdvds
    wbr
    #
    @9
    @6
    cM
    cN
    dvdsnegb
    @9
    @6
    @10
    @3
    @8
    cM
    cdvds
    breq2
    bicomd
    sylan9bb
    ex
    @1
    @4
    @9
    wo
    @0
    @1
    cN
    cN
    zre
    absord
    adantl
    mpjaod
end

include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "1nn0.mm"
include "a1i.mm"
include "simpr.mm"
include "cz.mm"
include "nn0z.mm"
include "1dvds.mm"
include "syl.mm"
include "adantr.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "ex.mm"
include "id.mm"
include "1z.mm"
include "iddvds.mm"
include "ax-mp.mm"
include "syl6eqbr.mm"
include "impbid1.mm"

theorem dvds1
  let cM: class M


  assert |- ( M e. NN0 -> ( M || 1 <-> M = 1 ) )

  proof
    cM
    cn0
    wcel
    #
    cM
    c1
    cdvds
    wbr
    #
    cM
    c1
    wceq
    #
    @0
    @1
    @2
    @0
    @1
    wa
    #
    @0
    c1
    cn0
    wcel
    #
    @1
    c1
    cM
    cdvds
    wbr
    #
    @2
    @0
    @1
    simpl
    @4
    @3
    1nn0
    a1i
    @0
    @1
    simpr
    @0
    @5
    @1
    @0
    cM
    cz
    wcel
    @5
    cM
    nn0z
    cM
    1dvds
    syl
    adantr
    cM
    c1
    dvdseq
    syl22anc
    ex
    @2
    cM
    c1
    c1
    cdvds
    @2
    id
    c1
    cz
    wcel
    c1
    c1
    cdvds
    wbr
    1z
    c1
    iddvds
    ax-mp
    syl6eqbr
    impbid1
end

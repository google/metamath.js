include "cuz.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "wn.mm"
include "uz0.mm"
include "adantl.mm"
include "neneq.mm"
include "adantr.mm"
include "condan.mm"
include "id.mm"
include "eqid.mm"
include "uzn0d.mm"
include "impbii.mm"

theorem uzn0bi
  let cM: class M


  assert |- ( ( ZZ>= ` M ) =/= (/) <-> M e. ZZ )

  proof
    cM
    cuz
    cfv
    #
    c0
    wne
    #
    cM
    cz
    wcel
    #
    @1
    @2
    @0
    c0
    wceq
    #
    @2
    wn
    #
    @3
    @1
    cM
    uz0
    adantl
    @1
    @3
    wn
    @4
    @0
    c0
    neneq
    adantr
    condan
    @2
    cM
    @0
    @2
    id
    @0
    eqid
    uzn0d
    impbii
end

include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "adantr.mm"
include "simpr.mm"
include "reclt0d.mm"
include "ex.mm"
include "wn.mm"
include "0red.mm"
include "wne.mm"
include "necomd.mm"
include "lttri5d.mm"
include "cle.mm"
include "rereccld.mm"
include "recgt0d.mm"
include "ltled.mm"
include "lenltd.mm"
include "mpbid.mm"
include "syldan.mm"
include "con4d.mm"
include "imp.mm"
include "impbid.mm"

theorem reclt0
  let wph: wff ph
  let cA: class A
  assume reclt0.1: |- ( ph -> A e. RR )
  assume reclt0.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( A < 0 <-> ( 1 / A ) < 0 ) )

  proof
    wph
    cA
    cc0
    clt
    wbr
    #
    c1
    cA
    cdiv
    co
    #
    cc0
    clt
    wbr
    #
    wph
    @0
    @2
    wph
    @0
    wa
    cA
    wph
    cA
    cr
    wcel
    #
    @0
    reclt0.1
    adantr
    wph
    @0
    simpr
    reclt0d
    ex
    wph
    @2
    @0
    wph
    @2
    @0
    wph
    @0
    @2
    wph
    @0
    wn
    #
    @2
    wn
    #
    wph
    @4
    cc0
    cA
    clt
    wbr
    #
    @5
    wph
    @4
    wa
    #
    cc0
    cA
    @7
    0red
    wph
    @3
    @4
    reclt0.1
    adantr
    wph
    cc0
    cA
    wne
    @4
    wph
    cA
    cc0
    reclt0.2
    necomd
    adantr
    wph
    @4
    simpr
    lttri5d
    wph
    @6
    wa
    #
    cc0
    @1
    cle
    wbr
    @5
    @8
    cc0
    @1
    @8
    0red
    #
    wph
    @1
    cr
    wcel
    @6
    wph
    cA
    reclt0.1
    reclt0.2
    rereccld
    adantr
    #
    @8
    cA
    wph
    @3
    @6
    reclt0.1
    adantr
    wph
    @6
    simpr
    recgt0d
    ltled
    @8
    cc0
    @1
    @9
    @10
    lenltd
    mpbid
    syldan
    ex
    con4d
    imp
    ex
    impbid
end

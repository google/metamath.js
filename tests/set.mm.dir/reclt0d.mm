include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "0lt1.mm"
include "a1i.mm"
include "cle.mm"
include "simpr.mm"
include "0red.mm"
include "cr.mm"
include "wcel.mm"
include "1red.mm"
include "lt0ne0d.mm"
include "redivcld.mm"
include "adantr.mm"
include "lenltd.mm"
include "mpbird.mm"
include "cmul.mm"
include "wceq.mm"
include "recnd.mm"
include "recidd.mm"
include "eqcomd.mm"
include "wo.mm"
include "ltled.mm"
include "jca.mm"
include "orcd.mm"
include "wb.mm"
include "mulle0b.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "mpbid.mm"
include "syldan.mm"
include "condan.mm"

theorem reclt0d
  let wph: wff ph
  let cA: class A
  assume reclt0d.1: |- ( ph -> A e. RR )
  assume reclt0d.2: |- ( ph -> A < 0 )


  assert |- ( ph -> ( 1 / A ) < 0 )

  proof
    wph
    c1
    cA
    cdiv
    co
    #
    cc0
    clt
    wbr
    #
    cc0
    c1
    clt
    wbr
    #
    @2
    wph
    @1
    wn
    #
    wa
    #
    0lt1
    a1i
    wph
    @3
    cc0
    @0
    cle
    wbr
    #
    @2
    wn
    #
    @4
    @5
    @3
    wph
    @3
    simpr
    @4
    cc0
    @0
    @4
    0red
    wph
    @0
    cr
    wcel
    #
    @3
    wph
    c1
    cA
    wph
    1red
    #
    reclt0d.1
    wph
    cA
    reclt0d.2
    lt0ne0d
    #
    redivcld
    #
    adantr
    lenltd
    mpbird
    wph
    @5
    wa
    #
    c1
    cc0
    cle
    wbr
    @6
    @11
    c1
    cA
    @0
    cmul
    co
    #
    cc0
    cle
    wph
    c1
    @12
    wceq
    @5
    wph
    @12
    c1
    wph
    cA
    wph
    cA
    reclt0d.1
    recnd
    @9
    recidd
    eqcomd
    adantr
    @11
    @12
    cc0
    cle
    wbr
    #
    cA
    cc0
    cle
    wbr
    #
    @5
    wa
    #
    cc0
    cA
    cle
    wbr
    @0
    cc0
    cle
    wbr
    wa
    #
    wo
    #
    @11
    @15
    @16
    @11
    @14
    @5
    wph
    @14
    @5
    wph
    cA
    cc0
    reclt0d.1
    wph
    0red
    reclt0d.2
    ltled
    adantr
    wph
    @5
    simpr
    jca
    orcd
    wph
    @13
    @17
    wb
    #
    @5
    wph
    cA
    cr
    wcel
    @7
    @18
    reclt0d.1
    @10
    cA
    @0
    mulle0b
    syl2anc
    adantr
    mpbird
    eqbrtrd
    @11
    c1
    cc0
    wph
    c1
    cr
    wcel
    @5
    @8
    adantr
    @11
    0red
    lenltd
    mpbid
    syldan
    condan
end

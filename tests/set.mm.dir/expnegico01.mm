include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cico.mm"
include "cr.mm"
include "cle.mm"
include "wne.mm"
include "wa.mm"
include "eluzelre.mm"
include "adantr.mm"
include "eluz2nn.mm"
include "nnne0d.mm"
include "simpr.mm"
include "3jca.mm"
include "3adant3.mm"
include "reexpclz.mm"
include "syl.mm"
include "0red.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "reexpclzd.mm"
include "nngt0d.mm"
include "expgt0.mm"
include "syl3anc.mm"
include "ltled.mm"
include "0zd.mm"
include "eluz2gt1.mm"
include "simp3.mm"
include "ltexp2a.mm"
include "syl32anc.mm"
include "wceq.mm"
include "eluzelcn.mm"
include "exp0d.mm"
include "eqcomd.mm"
include "breqtrrd.mm"
include "cxr.mm"
include "wb.mm"
include "0re.mm"
include "1re.mm"
include "rexri.mm"
include "pm3.2i.mm"
include "elico2.mm"
include "mp1i.mm"
include "mpbir3and.mm"

theorem expnegico01
  let cB: class B
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ N e. ZZ /\ N < 0 ) -> ( B ^ N ) e. ( 0 [,) 1 ) )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    clt
    wbr
    #
    w3a
    #
    cB
    cN
    cexp
    co
    #
    cc0
    c1
    cico
    co
    wcel
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    c1
    clt
    wbr
    #
    @3
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    @1
    w3a
    #
    @6
    @0
    @1
    @11
    @2
    @0
    @1
    wa
    @9
    @10
    @1
    @0
    @9
    @1
    c2
    cB
    eluzelre
    #
    adantr
    @0
    @10
    @1
    @0
    cB
    cB
    eluz2nn
    #
    nnne0d
    #
    adantr
    @0
    @1
    simpr
    3jca
    3adant3
    cB
    cN
    reexpclz
    syl
    @3
    cc0
    @4
    @3
    0red
    @3
    cB
    cN
    @0
    @1
    @9
    @2
    @12
    3ad2ant1
    #
    @0
    @1
    @10
    @2
    @14
    3ad2ant1
    @0
    @1
    @2
    simp2
    #
    reexpclzd
    @3
    @9
    @1
    cc0
    cB
    clt
    wbr
    #
    cc0
    @4
    clt
    wbr
    @15
    @16
    @0
    @1
    @17
    @2
    @0
    cB
    @13
    nngt0d
    3ad2ant1
    cB
    cN
    expgt0
    syl3anc
    ltled
    @3
    @4
    cB
    cc0
    cexp
    co
    #
    c1
    clt
    @3
    @9
    @1
    cc0
    cz
    wcel
    c1
    cB
    clt
    wbr
    #
    @2
    @4
    @18
    clt
    wbr
    @15
    @16
    @3
    0zd
    @0
    @1
    @19
    @2
    cB
    eluz2gt1
    3ad2ant1
    @0
    @1
    @2
    simp3
    cB
    cN
    cc0
    ltexp2a
    syl32anc
    @0
    @1
    c1
    @18
    wceq
    @2
    @0
    @18
    c1
    @0
    cB
    c2
    cB
    eluzelcn
    exp0d
    eqcomd
    3ad2ant1
    breqtrrd
    cc0
    cr
    wcel
    #
    c1
    cxr
    wcel
    #
    wa
    @5
    @6
    @7
    @8
    w3a
    wb
    @3
    @20
    @21
    0re
    c1
    1re
    rexri
    pm3.2i
    cc0
    c1
    @4
    elico2
    mp1i
    mpbir3and
end

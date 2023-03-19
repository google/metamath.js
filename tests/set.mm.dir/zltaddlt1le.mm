include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "w3a.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cr.mm"
include "wi.mm"
include "wa.mm"
include "zre.mm"
include "adantr.mm"
include "elioore.mm"
include "adantl.mm"
include "readdcld.mm"
include "3adant2.mm"
include "3ad2ant2.mm"
include "ltle.mm"
include "syl2anc.mm"
include "crp.mm"
include "cxr.mm"
include "elioo3g.mm"
include "simpl.mm"
include "simplbiim.mm"
include "elrpd.mm"
include "addlelt.mm"
include "syl3an.mm"
include "wb.mm"
include "zltp1le.mm"
include "3adant3.mm"
include "3ad2ant3.mm"
include "1red.mm"
include "3ad2ant1.mm"
include "simpr.mm"
include "ltadd2dd.mm"
include "peano2z.mm"
include "zred.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylbid.mm"
include "syld.mm"
include "impbid.mm"

theorem zltaddlt1le
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ /\ A e. ( 0 (,) 1 ) ) -> ( ( M + A ) < N <-> ( M + A ) <_ N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cA
    cc0
    c1
    cioo
    co
    wcel
    #
    w3a
    #
    cM
    cA
    caddc
    co
    #
    cN
    clt
    wbr
    #
    @4
    cN
    cle
    wbr
    #
    @3
    @4
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @5
    @6
    wi
    @0
    @2
    @7
    @1
    @0
    @2
    wa
    cM
    cA
    @0
    cM
    cr
    wcel
    #
    @2
    cM
    zre
    #
    adantr
    @2
    cA
    cr
    wcel
    #
    @0
    cA
    cc0
    c1
    elioore
    #
    adantl
    readdcld
    3adant2
    #
    @1
    @0
    @8
    @2
    cN
    zre
    #
    3ad2ant2
    #
    @4
    cN
    ltle
    syl2anc
    @3
    @6
    cM
    cN
    clt
    wbr
    #
    @5
    @0
    @9
    @1
    @8
    @2
    cA
    crp
    wcel
    @6
    @16
    wi
    @10
    @14
    @2
    cA
    @12
    @2
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    cA
    cxr
    wcel
    w3a
    #
    cc0
    cA
    clt
    wbr
    #
    cA
    c1
    clt
    wbr
    #
    wa
    #
    @18
    cc0
    c1
    cA
    elioo3g
    #
    @18
    @19
    simpl
    simplbiim
    elrpd
    cA
    cM
    cN
    addlelt
    syl3an
    @3
    @16
    cM
    c1
    caddc
    co
    #
    cN
    cle
    wbr
    #
    @5
    @0
    @1
    @16
    @23
    wb
    @2
    cM
    cN
    zltp1le
    3adant3
    @3
    @4
    @22
    clt
    wbr
    #
    @23
    @5
    @3
    cA
    c1
    cM
    @2
    @0
    @11
    @1
    @12
    3ad2ant3
    @3
    1red
    @0
    @1
    @9
    @2
    @10
    3ad2ant1
    @2
    @0
    @19
    @1
    @2
    @17
    @20
    @19
    @21
    @18
    @19
    simpr
    simplbiim
    3ad2ant3
    ltadd2dd
    @3
    @7
    @22
    cr
    wcel
    #
    @8
    @24
    @23
    wa
    @5
    wi
    @13
    @0
    @1
    @25
    @2
    @0
    @22
    cM
    peano2z
    zred
    3ad2ant1
    @15
    @4
    @22
    cN
    ltletr
    syl3anc
    mpand
    sylbid
    syld
    impbid
end

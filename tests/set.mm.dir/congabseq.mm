include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "ad2antrr.mm"
include "3ad2ant3.mm"
include "cle.mm"
include "wn.mm"
include "cc0.mm"
include "cr.mm"
include "zsubcl.mm"
include "3adant1.mm"
include "zcnd.mm"
include "abscld.mm"
include "adantr.mm"
include "nnre.mm"
include "3ad2ant1.mm"
include "ltnled.mm"
include "biimpa.mm"
include "wne.mm"
include "nnz.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "3jca.mm"
include "simpllr.mm"
include "dvdsleabs.mm"
include "sylc.mm"
include "ex.mm"
include "necon1bd.mm"
include "mpd.mm"
include "subeq0d.mm"
include "oveq1.mm"
include "adantl.mm"
include "subidd.mm"
include "eqtrd.mm"
include "abs00bd.mm"
include "nngt0.mm"
include "eqbrtrd.mm"
include "impbida.mm"

theorem congabseq
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. ZZ /\ C e. ZZ ) /\ A || ( B - C ) ) -> ( ( abs ` ( B - C ) ) < A <-> B = C ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @4
    cabs
    cfv
    #
    cA
    clt
    wbr
    #
    cB
    cC
    wceq
    #
    @6
    @8
    wa
    #
    cB
    cC
    @3
    cB
    cc
    wcel
    #
    @5
    @8
    @1
    @0
    @11
    @2
    cB
    zcn
    3ad2ant2
    ad2antrr
    @3
    cC
    cc
    wcel
    #
    @5
    @8
    @2
    @0
    @12
    @1
    cC
    zcn
    3ad2ant3
    #
    ad2antrr
    @10
    cA
    @7
    cle
    wbr
    #
    wn
    #
    @4
    cc0
    wceq
    @6
    @8
    @15
    @6
    @7
    cA
    @3
    @7
    cr
    wcel
    @5
    @3
    @4
    @3
    @4
    @1
    @2
    @4
    cz
    wcel
    #
    @0
    cB
    cC
    zsubcl
    3adant1
    #
    zcnd
    abscld
    adantr
    @3
    cA
    cr
    wcel
    #
    @5
    @0
    @1
    @18
    @2
    cA
    nnre
    3ad2ant1
    adantr
    ltnled
    biimpa
    @10
    @14
    @4
    cc0
    @10
    @4
    cc0
    wne
    #
    @14
    @10
    @19
    wa
    #
    cA
    cz
    wcel
    #
    @16
    @19
    w3a
    @5
    @14
    @20
    @21
    @16
    @19
    @3
    @21
    @5
    @8
    @19
    @0
    @1
    @21
    @2
    cA
    nnz
    3ad2ant1
    ad3antrrr
    @3
    @16
    @5
    @8
    @19
    @17
    ad3antrrr
    @10
    @19
    simpr
    3jca
    @3
    @5
    @8
    @19
    simpllr
    cA
    @4
    dvdsleabs
    sylc
    ex
    necon1bd
    mpd
    subeq0d
    @6
    @9
    wa
    #
    @7
    cc0
    cA
    clt
    @22
    @4
    @22
    @4
    cC
    cC
    cmin
    co
    #
    cc0
    @9
    @4
    @23
    wceq
    @6
    cB
    cC
    cC
    cmin
    oveq1
    adantl
    @22
    cC
    @3
    @12
    @5
    @9
    @13
    ad2antrr
    subidd
    eqtrd
    abs00bd
    @3
    cc0
    cA
    clt
    wbr
    #
    @5
    @9
    @0
    @1
    @24
    @2
    cA
    nngt0
    3ad2ant1
    ad2antrr
    eqbrtrd
    impbida
end

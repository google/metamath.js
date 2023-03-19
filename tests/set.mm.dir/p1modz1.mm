include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "clt.mm"
include "caddc.mm"
include "co.mm"
include "cmo.mm"
include "wceq.mm"
include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "dvdszrcl.mm"
include "cc0.mm"
include "cn.mm"
include "cr.mm"
include "w3a.mm"
include "0red.mm"
include "1red.mm"
include "zre.mm"
include "adantr.mm"
include "3jca.mm"
include "0lt1.mm"
include "a1i.mm"
include "anim1i.mm"
include "lttr.mm"
include "sylc.mm"
include "ex.mm"
include "elnnz.mm"
include "simplbi2.mm"
include "syld.mm"
include "imp.mm"
include "dvdsmod0.mm"
include "sylan.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "adantl.mm"
include "crp.mm"
include "nnrpd.mm"
include "modaddmod.mm"
include "syl.mm"
include "1mod.mm"
include "3eqtr3d.mm"
include "com23.mm"
include "mpcom.mm"

theorem p1modz1
  let cA: class A
  let cM: class M


  assert |- ( ( M || A /\ 1 < M ) -> ( ( A + 1 ) mod M ) = 1 )

  proof
    cM
    cA
    cdvds
    wbr
    #
    c1
    cM
    clt
    wbr
    #
    cA
    c1
    caddc
    co
    cM
    cmo
    co
    #
    c1
    wceq
    #
    cM
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    wa
    #
    @0
    @1
    @3
    wi
    cM
    cA
    dvdszrcl
    @6
    @1
    @0
    @3
    @6
    @1
    @0
    @3
    wi
    @6
    @1
    wa
    #
    @0
    cA
    cM
    cmo
    co
    #
    cc0
    wceq
    #
    @3
    @7
    @0
    @9
    @7
    cM
    cn
    wcel
    #
    @0
    @9
    @6
    @1
    @10
    @4
    @1
    @10
    wi
    @5
    @4
    @1
    cc0
    cM
    clt
    wbr
    #
    @10
    @4
    @1
    @11
    @4
    @1
    wa
    #
    cc0
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    w3a
    cc0
    c1
    clt
    wbr
    #
    @1
    wa
    @11
    @12
    @13
    @14
    @15
    @12
    0red
    @12
    1red
    @4
    @15
    @1
    cM
    zre
    #
    adantr
    3jca
    @4
    @16
    @1
    @16
    @4
    0lt1
    a1i
    anim1i
    cc0
    c1
    cM
    lttr
    sylc
    ex
    @10
    @4
    @11
    cM
    elnnz
    simplbi2
    syld
    adantr
    imp
    #
    cM
    cA
    dvdsmod0
    sylan
    ex
    @7
    @9
    @3
    @7
    @9
    wa
    #
    @8
    c1
    caddc
    co
    #
    cM
    cmo
    co
    #
    c1
    cM
    cmo
    co
    #
    @2
    c1
    @9
    @21
    @22
    wceq
    @7
    @9
    @20
    c1
    cM
    cmo
    @9
    @20
    cc0
    c1
    caddc
    co
    c1
    @8
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    oveq1d
    adantl
    @19
    cA
    cr
    wcel
    #
    @14
    cM
    crp
    wcel
    #
    w3a
    #
    @21
    @2
    wceq
    @7
    @25
    @9
    @7
    @23
    @14
    @24
    @6
    @23
    @1
    @5
    @23
    @4
    cA
    zre
    adantl
    adantr
    @7
    1red
    @7
    cM
    @18
    nnrpd
    3jca
    adantr
    cA
    c1
    cM
    modaddmod
    syl
    @7
    @22
    c1
    wceq
    #
    @9
    @6
    @15
    @1
    @26
    @4
    @15
    @5
    @17
    adantr
    cM
    1mod
    sylan
    adantr
    3eqtr3d
    ex
    syld
    ex
    com23
    mpcom
    imp
end

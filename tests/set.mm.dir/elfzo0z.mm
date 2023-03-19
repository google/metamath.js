include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cz.mm"
include "elfzo0.mm"
include "nnz.mm"
include "3anim2i.mm"
include "simp1.mm"
include "cle.mm"
include "wa.mm"
include "wi.mm"
include "elnn0z.mm"
include "cr.mm"
include "0red.mm"
include "zre.mm"
include "adantr.mm"
include "adantl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "elnnz.mm"
include "simplbi2.mm"
include "syld.mm"
include "expd.mm"
include "impancom.mm"
include "sylbi.mm"
include "3imp.mm"
include "simp3.mm"
include "3jca.mm"
include "impbii.mm"
include "bitri.mm"

theorem elfzo0z
  let cA: class A
  let cB: class B


  assert |- ( A e. ( 0 ..^ B ) <-> ( A e. NN0 /\ B e. ZZ /\ A < B ) )

  proof
    cA
    cc0
    cB
    cfzo
    co
    wcel
    cA
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    @0
    cB
    cz
    wcel
    #
    @2
    w3a
    #
    cA
    cB
    elfzo0
    @3
    @5
    @1
    @4
    @0
    @2
    cB
    nnz
    3anim2i
    @5
    @0
    @1
    @2
    @0
    @4
    @2
    simp1
    @0
    @4
    @2
    @1
    @0
    cA
    cz
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    @4
    @2
    @1
    wi
    #
    wi
    cA
    elnn0z
    @6
    @4
    @7
    @8
    @6
    @4
    wa
    #
    @7
    @2
    @1
    @9
    @7
    @2
    wa
    #
    cc0
    cB
    clt
    wbr
    #
    @1
    @9
    cc0
    cr
    wcel
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @10
    @11
    wi
    @9
    0red
    @6
    @12
    @4
    cA
    zre
    adantr
    @4
    @13
    @6
    cB
    zre
    adantl
    cc0
    cA
    cB
    lelttr
    syl3anc
    @4
    @11
    @1
    wi
    @6
    @1
    @4
    @11
    cB
    elnnz
    simplbi2
    adantl
    syld
    expd
    impancom
    sylbi
    3imp
    @0
    @4
    @2
    simp3
    3jca
    impbii
    bitri
end

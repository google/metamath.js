include "cr.mm"
include "cz.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wn.mm"
include "eldif.mm"
include "zre.mm"
include "readdcl.mm"
include "sylan2.mm"
include "adantlr.mm"
include "wi.mm"
include "cmin.mm"
include "zsubcl.mm"
include "expcom.mm"
include "adantl.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "zcn.mm"
include "pncan.mm"
include "syl2an.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "con3d.mm"
include "ex.mm"
include "com23.mm"
include "imp31.mm"
include "jca.mm"
include "sylanb.mm"
include "sylibr.mm"

theorem nzadd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( RR \ ZZ ) /\ B e. ZZ ) -> ( A + B ) e. ( RR \ ZZ ) )

  proof
    cA
    cr
    cz
    cdif
    #
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    cA
    cB
    caddc
    co
    #
    cr
    wcel
    #
    @3
    cz
    wcel
    #
    wn
    #
    wa
    #
    @3
    @0
    wcel
    @1
    cA
    cr
    wcel
    #
    cA
    cz
    wcel
    #
    wn
    #
    wa
    #
    @2
    @7
    cA
    cr
    cz
    eldif
    @11
    @2
    wa
    @4
    @6
    @8
    @2
    @4
    @10
    @2
    @8
    cB
    cr
    wcel
    @4
    cB
    zre
    cA
    cB
    readdcl
    sylan2
    adantlr
    @8
    @10
    @2
    @6
    @8
    @2
    @10
    @6
    @8
    @2
    @10
    @6
    wi
    @8
    @2
    wa
    #
    @5
    @9
    @12
    @5
    @3
    cB
    cmin
    co
    #
    cz
    wcel
    #
    @9
    @2
    @5
    @14
    wi
    @8
    @5
    @2
    @14
    @3
    cB
    zsubcl
    expcom
    adantl
    @12
    @13
    cA
    cz
    @8
    cA
    cc
    wcel
    cB
    cc
    wcel
    @13
    cA
    wceq
    @2
    cA
    recn
    cB
    zcn
    cA
    cB
    pncan
    syl2an
    eleq1d
    sylibd
    con3d
    ex
    com23
    imp31
    jca
    sylanb
    @3
    cr
    cz
    eldif
    sylibr
end

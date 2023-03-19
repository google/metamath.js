include "cr.mm"
include "cq.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "wn.mm"
include "eldif.mm"
include "qre.mm"
include "readdcl.mm"
include "sylan2.mm"
include "adantlr.mm"
include "wi.mm"
include "cmin.mm"
include "qsubcl.mm"
include "expcom.mm"
include "adantl.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "qcn.mm"
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

theorem irradd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( RR \ QQ ) /\ B e. QQ ) -> ( A + B ) e. ( RR \ QQ ) )

  proof
    cA
    cr
    cq
    cdif
    #
    wcel
    #
    cB
    cq
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
    cq
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
    cq
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
    cq
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
    qre
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
    cq
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
    qsubcl
    expcom
    adantl
    @12
    @13
    cA
    cq
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
    qcn
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
    cq
    eldif
    sylibr
end

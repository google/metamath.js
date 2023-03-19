include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "resqcl.mm"
include "sqge0.mm"
include "jca.mm"
include "add20.mm"
include "syl2an.mm"
include "cc.mm"
include "recn.mm"
include "sqeq0.mm"
include "syl.mm"
include "bi2anan9.mm"
include "bitr2d.mm"

theorem sumsqeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( A = 0 /\ B = 0 ) <-> ( ( A ^ 2 ) + ( B ^ 2 ) ) = 0 ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    cc0
    wceq
    #
    @2
    cc0
    wceq
    #
    @3
    cc0
    wceq
    #
    wa
    #
    cA
    cc0
    wceq
    #
    cB
    cc0
    wceq
    #
    wa
    @0
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    @4
    @7
    wb
    @1
    @0
    @10
    @11
    cA
    resqcl
    cA
    sqge0
    jca
    @1
    @12
    @13
    cB
    resqcl
    cB
    sqge0
    jca
    @2
    @3
    add20
    syl2an
    @0
    @5
    @8
    @1
    @6
    @9
    @0
    cA
    cc
    wcel
    @5
    @8
    wb
    cA
    recn
    cA
    sqeq0
    syl
    @1
    cB
    cc
    wcel
    @6
    @9
    wb
    cB
    recn
    cB
    sqeq0
    syl
    bi2anan9
    bitr2d
end

include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "wi.mm"
include "3simpa.mm"
include "rehalfcl.mm"
include "jca.mm"
include "3ad2ant3.mm"
include "lt2add.mm"
include "syl2anc.mm"
include "wb.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "2halves.mm"
include "syl.mm"
include "breq2d.mm"
include "sylibd.mm"

theorem lt2halves
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A < ( C / 2 ) /\ B < ( C / 2 ) ) -> ( A + B ) < C ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cC
    c2
    cdiv
    co
    #
    clt
    wbr
    cB
    @4
    clt
    wbr
    wa
    #
    cA
    cB
    caddc
    co
    #
    @4
    @4
    caddc
    co
    #
    clt
    wbr
    #
    @6
    cC
    clt
    wbr
    #
    @3
    @0
    @1
    wa
    @4
    cr
    wcel
    #
    @10
    wa
    #
    @5
    @8
    wi
    @0
    @1
    @2
    3simpa
    @2
    @0
    @11
    @1
    @2
    @10
    @10
    cC
    rehalfcl
    #
    @12
    jca
    3ad2ant3
    cA
    cB
    @4
    @4
    lt2add
    syl2anc
    @2
    @0
    @8
    @9
    wb
    @1
    @2
    @7
    cC
    @6
    clt
    @2
    cC
    cc
    wcel
    @7
    cC
    wceq
    cC
    recn
    cC
    2halves
    syl
    breq2d
    3ad2ant3
    sylibd
end

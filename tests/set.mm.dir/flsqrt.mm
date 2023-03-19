include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cn0.mm"
include "csqrt.mm"
include "cfv.mm"
include "cfl.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "c2.mm"
include "cexp.mm"
include "cz.mm"
include "wb.mm"
include "resqrtcl.mm"
include "nn0z.mm"
include "flbi.mm"
include "syl2an.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "sqrtsq.mm"
include "eqcomd.mm"
include "syl.mm"
include "breq1d.mm"
include "adantl.mm"
include "nn0sqcl.mm"
include "nn0red.mm"
include "sqge0d.mm"
include "anim2i.mm"
include "ancomd.mm"
include "sqrtle.mm"
include "bitr4d.mm"
include "peano2nn0.mm"
include "1red.mm"
include "0le1.mm"
include "a1i.mm"
include "addge0d.mm"
include "sqrtsqd.mm"
include "breq2d.mm"
include "2nn0.mm"
include "nn0expcld.mm"
include "sqrtlt.mm"
include "sylan2.mm"
include "anbi12d.mm"
include "bitrd.mm"

theorem flsqrt
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ B e. NN0 ) -> ( ( |_ ` ( sqrt ` A ) ) = B <-> ( ( B ^ 2 ) <_ A /\ A < ( ( B + 1 ) ^ 2 ) ) ) )

  proof
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    #
    cB
    cn0
    wcel
    #
    wa
    #
    cA
    csqrt
    cfv
    #
    cfl
    cfv
    cB
    wceq
    #
    cB
    @3
    cle
    wbr
    #
    @3
    cB
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    cB
    c2
    cexp
    co
    #
    cA
    cle
    wbr
    #
    cA
    @6
    c2
    cexp
    co
    #
    clt
    wbr
    #
    wa
    @0
    @3
    cr
    wcel
    cB
    cz
    wcel
    @4
    @8
    wb
    @1
    cA
    resqrtcl
    cB
    nn0z
    @3
    cB
    flbi
    syl2an
    @2
    @5
    @10
    @7
    @12
    @2
    @5
    @9
    csqrt
    cfv
    #
    @3
    cle
    wbr
    #
    @10
    @1
    @5
    @14
    wb
    @0
    @1
    cB
    @13
    @3
    cle
    @1
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    #
    cB
    @13
    wceq
    @1
    @15
    @16
    cB
    nn0re
    #
    cB
    nn0ge0
    #
    jca
    @17
    @13
    cB
    cB
    sqrtsq
    eqcomd
    syl
    breq1d
    adantl
    @2
    @9
    cr
    wcel
    #
    cc0
    @9
    cle
    wbr
    #
    wa
    #
    @0
    wa
    @10
    @14
    wb
    @2
    @0
    @22
    @1
    @22
    @0
    @1
    @20
    @21
    @1
    @9
    cB
    nn0sqcl
    nn0red
    @1
    cB
    @18
    sqge0d
    jca
    anim2i
    ancomd
    @9
    cA
    sqrtle
    syl
    bitr4d
    @2
    @7
    @3
    @11
    csqrt
    cfv
    #
    clt
    wbr
    #
    @12
    @1
    @7
    @24
    wb
    @0
    @1
    @6
    @23
    @3
    clt
    @1
    @23
    @6
    @1
    @6
    @1
    @6
    cB
    peano2nn0
    #
    nn0red
    #
    @1
    cB
    c1
    @18
    @1
    1red
    @19
    cc0
    c1
    cle
    wbr
    @1
    0le1
    a1i
    addge0d
    sqrtsqd
    eqcomd
    breq2d
    adantl
    @1
    @0
    @11
    cr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    wa
    @12
    @24
    wb
    @1
    @27
    @28
    @1
    @11
    @1
    @6
    c2
    @25
    c2
    cn0
    wcel
    @1
    2nn0
    a1i
    nn0expcld
    nn0red
    @1
    @6
    @26
    sqge0d
    jca
    cA
    @11
    sqrtlt
    sylan2
    bitr4d
    anbi12d
    bitrd
end

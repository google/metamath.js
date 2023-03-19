include "cr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cfl.mm"
include "cfv.mm"
include "cmo.mm"
include "cdiv.mm"
include "cmin.mm"
include "c1.mm"
include "crp.mm"
include "wceq.mm"
include "cn0.mm"
include "nnre.mm"
include "nnnn0.mm"
include "reexpcl.mm"
include "syl2an.mm"
include "remulcl.mm"
include "stoic3.mm"
include "3comr.mm"
include "reflcl.mm"
include "syl.mm"
include "nnrp.mm"
include "3ad2ant2.mm"
include "modval.mm"
include "syl2anc.mm"
include "simp2.mm"
include "fldiv.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "nncn.mm"
include "expcl.mm"
include "3adant1.mm"
include "recn.mm"
include "3ad2ant1.mm"
include "nnne0.mm"
include "jca.mm"
include "div23.mm"
include "syl3anc.mm"
include "cz.mm"
include "nnz.mm"
include "expm1.mm"
include "3expa.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"

theorem digit2
  let cA: class A
  let cB: class B
  let cK: class K


  assert |- ( ( A e. RR /\ B e. NN /\ K e. NN ) -> ( ( |_ ` ( ( B ^ K ) x. A ) ) mod B ) = ( ( |_ ` ( ( B ^ K ) x. A ) ) - ( B x. ( |_ ` ( ( B ^ ( K - 1 ) ) x. A ) ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cn
    wcel
    #
    cK
    cn
    wcel
    #
    w3a
    #
    cB
    cK
    cexp
    co
    #
    cA
    cmul
    co
    #
    cfl
    cfv
    #
    cB
    cmo
    co
    #
    @6
    cB
    @6
    cB
    cdiv
    co
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @6
    cB
    cB
    cK
    c1
    cmin
    co
    cexp
    co
    #
    cA
    cmul
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    cmin
    co
    @3
    @6
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    @7
    @10
    wceq
    @3
    @5
    cr
    wcel
    #
    @15
    @1
    @2
    @0
    @17
    @1
    @2
    @4
    cr
    wcel
    #
    @0
    @17
    @1
    cB
    cr
    wcel
    cK
    cn0
    wcel
    #
    @18
    @2
    cB
    nnre
    cK
    nnnn0
    #
    cB
    cK
    reexpcl
    syl2an
    @4
    cA
    remulcl
    stoic3
    3comr
    #
    @5
    reflcl
    syl
    @1
    @0
    @16
    @2
    cB
    nnrp
    3ad2ant2
    @6
    cB
    modval
    syl2anc
    @3
    @9
    @14
    @6
    cmin
    @3
    @8
    @13
    cB
    cmul
    @3
    @8
    @5
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    @13
    @3
    @17
    @1
    @8
    @23
    wceq
    @21
    @0
    @1
    @2
    simp2
    @5
    cB
    fldiv
    syl2anc
    @3
    @22
    @12
    cfl
    @3
    @22
    @4
    cB
    cdiv
    co
    #
    cA
    cmul
    co
    #
    @12
    @3
    @4
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    @22
    @25
    wceq
    @1
    @2
    @26
    @0
    @1
    @28
    @19
    @26
    @2
    cB
    nncn
    #
    @20
    cB
    cK
    expcl
    syl2an
    3adant1
    @0
    @1
    @27
    @2
    cA
    recn
    3ad2ant1
    @1
    @0
    @30
    @2
    @1
    @28
    @29
    @31
    cB
    nnne0
    jca
    #
    3ad2ant2
    @4
    cA
    cB
    div23
    syl3anc
    @3
    @11
    @24
    cA
    cmul
    @1
    @2
    @11
    @24
    wceq
    #
    @0
    @1
    @30
    cK
    cz
    wcel
    #
    @33
    @2
    @32
    cK
    nnz
    @28
    @29
    @34
    @33
    cB
    cK
    expm1
    3expa
    syl2an
    3adant1
    oveq1d
    eqtr4d
    fveq2d
    eqtrd
    oveq2d
    oveq2d
    eqtrd
end

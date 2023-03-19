include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cc0.mm"
include "cdiv.mm"
include "co.mm"
include "cfl.mm"
include "cfv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmo.mm"
include "cle.mm"
include "wbr.mm"
include "fldivle.mm"
include "clt.mm"
include "wb.mm"
include "refldivcl.mm"
include "simpl.mm"
include "rpregt0.mm"
include "adantl.mm"
include "lemuldiv2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "rpre.mm"
include "remulcld.mm"
include "subge0.mm"
include "syldan.mm"
include "modval.mm"
include "breqtrrd.mm"

theorem modge0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> 0 <_ ( A mod B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cc0
    cA
    cB
    cA
    cB
    cdiv
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
    #
    cA
    cB
    cmo
    co
    cle
    @2
    cc0
    @6
    cle
    wbr
    #
    @5
    cA
    cle
    wbr
    #
    @2
    @8
    @4
    @3
    cle
    wbr
    #
    cA
    cB
    fldivle
    @2
    @4
    cr
    wcel
    @0
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    wa
    #
    @8
    @9
    wb
    cA
    cB
    refldivcl
    #
    @0
    @1
    simpl
    @1
    @11
    @0
    cB
    rpregt0
    adantl
    @4
    cA
    cB
    lemuldiv2
    syl3anc
    mpbird
    @0
    @1
    @5
    cr
    wcel
    @7
    @8
    wb
    @2
    cB
    @4
    @1
    @10
    @0
    cB
    rpre
    adantl
    @12
    remulcld
    cA
    @5
    subge0
    syldan
    mpbird
    cA
    cB
    modval
    breqtrrd
end

include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cort.mm"
include "wceq.mm"
include "cva.mm"
include "pjch1.mm"
include "adantl.mm"
include "axpjpj.mm"
include "eqtr2d.mm"
include "wb.mm"
include "helch.mm"
include "pjcli.mm"
include "pjhcl.mm"
include "choccl.mm"
include "sylan.mm"
include "hvsubadd.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem pjo
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( ( projh ` ( _|_ ` H ) ) ` A ) = ( ( ( projh ` ~H ) ` A ) -h ( ( projh ` H ) ` A ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    cA
    chil
    cpjh
    cfv
    cfv
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cmv
    co
    #
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    @2
    @5
    @7
    wceq
    #
    @4
    @7
    cva
    co
    #
    @3
    wceq
    #
    @2
    @3
    cA
    @9
    @1
    @3
    cA
    wceq
    @0
    cA
    pjch1
    adantl
    cA
    cH
    axpjpj
    eqtr2d
    @2
    @3
    chil
    wcel
    #
    @4
    chil
    wcel
    @7
    chil
    wcel
    #
    @8
    @10
    wb
    @1
    @11
    @0
    cA
    chil
    helch
    pjcli
    adantl
    cA
    cH
    pjhcl
    @0
    @6
    cch
    wcel
    @1
    @12
    cH
    choccl
    cA
    @6
    pjhcl
    sylan
    @3
    @4
    @7
    hvsubadd
    syl3anc
    mpbird
    eqcomd
end

include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "cpjh.mm"
include "wceq.mm"
include "cch.mm"
include "chil.mm"
include "cheli.mm"
include "choccli.mm"
include "hvaddcl.mm"
include "syl2an.mm"
include "axpjpj.mm"
include "sylancr.mm"
include "eqid.mm"
include "wi.mm"
include "axpjcl.mm"
include "simpl.mm"
include "simpr.mm"
include "chocunii.mm"
include "syl22anc.mm"
include "mpan2i.mm"
include "mpd.mm"
include "simpld.mm"

theorem pjcompi
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjidm.1: |- H e. CH


  assert |- ( ( A e. H /\ B e. ( _|_ ` H ) ) -> ( ( projh ` H ) ` ( A +h B ) ) = A )

  proof
    cA
    cH
    wcel
    #
    cB
    cH
    cort
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cB
    cva
    co
    #
    cH
    cpjh
    cfv
    cfv
    #
    cA
    wceq
    #
    @4
    @1
    cpjh
    cfv
    cfv
    #
    cB
    wceq
    #
    @3
    @4
    @5
    @7
    cva
    co
    wceq
    #
    @6
    @8
    wa
    #
    @3
    cH
    cch
    wcel
    #
    @4
    chil
    wcel
    #
    @9
    pjidm.1
    @0
    cA
    chil
    wcel
    cB
    chil
    wcel
    @12
    @2
    cA
    cH
    pjidm.1
    cheli
    cB
    @1
    cH
    pjidm.1
    choccli
    #
    cheli
    cA
    cB
    hvaddcl
    syl2an
    #
    @4
    cH
    axpjpj
    sylancr
    @3
    @9
    @4
    @4
    wceq
    #
    @10
    @4
    eqid
    @3
    @5
    cH
    wcel
    #
    @7
    @1
    wcel
    #
    @0
    @2
    @9
    @15
    wa
    @10
    wi
    @3
    @11
    @12
    @16
    pjidm.1
    @14
    @4
    cH
    axpjcl
    sylancr
    @3
    @1
    cch
    wcel
    @12
    @17
    @13
    @14
    @4
    @1
    axpjcl
    sylancr
    @0
    @2
    simpl
    @0
    @2
    simpr
    @5
    @7
    cA
    cB
    @4
    cH
    pjidm.1
    chocunii
    syl22anc
    mpan2i
    mpd
    simpld
end

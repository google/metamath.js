include "clog.mm"
include "crn.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cc.mm"
include "cpi.mm"
include "cneg.mm"
include "cim.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "logrncn.mm"
include "recn.mm"
include "addcl.mm"
include "syl2an.mm"
include "ellogrn.mm"
include "simp2bi.mm"
include "adantr.mm"
include "cc0.mm"
include "wceq.mm"
include "imadd.mm"
include "reim0.mm"
include "adantl.mm"
include "oveq2d.mm"
include "imcld.mm"
include "recnd.mm"
include "addid1d.mm"
include "3eqtrd.mm"
include "breqtrrd.mm"
include "simp3bi.mm"
include "eqbrtrd.mm"
include "syl3anbrc.mm"

theorem logrnaddcl
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ran log /\ B e. RR ) -> ( A + B ) e. ran log )

  proof
    cA
    clog
    crn
    #
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    caddc
    co
    #
    cc
    wcel
    #
    cpi
    cneg
    #
    @4
    cim
    cfv
    #
    clt
    wbr
    @7
    cpi
    cle
    wbr
    @4
    @0
    wcel
    @1
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @5
    @2
    cA
    logrncn
    #
    cB
    recn
    #
    cA
    cB
    addcl
    syl2an
    @3
    @6
    cA
    cim
    cfv
    #
    @7
    clt
    @1
    @6
    @12
    clt
    wbr
    #
    @2
    @1
    @8
    @13
    @12
    cpi
    cle
    wbr
    #
    cA
    ellogrn
    #
    simp2bi
    adantr
    @3
    @7
    @12
    cB
    cim
    cfv
    #
    caddc
    co
    #
    @12
    cc0
    caddc
    co
    @12
    @1
    @8
    @9
    @7
    @17
    wceq
    @2
    @10
    @11
    cA
    cB
    imadd
    syl2an
    @3
    @16
    cc0
    @12
    caddc
    @2
    @16
    cc0
    wceq
    @1
    cB
    reim0
    adantl
    oveq2d
    @3
    @12
    @3
    @12
    @3
    cA
    @1
    @8
    @2
    @10
    adantr
    imcld
    recnd
    addid1d
    3eqtrd
    #
    breqtrrd
    @3
    @7
    @12
    cpi
    cle
    @18
    @1
    @14
    @2
    @1
    @8
    @13
    @14
    @15
    simp3bi
    adantr
    eqbrtrd
    @4
    ellogrn
    syl3anbrc
end

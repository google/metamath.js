include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "0red.mm"
include "id.mm"
include "wa.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "addid1d.mm"
include "iftrue.mm"
include "adantl.mm"
include "le0neg2.mm"
include "biimpa.mm"
include "simpr.mm"
include "wb.mm"
include "renegcl.mm"
include "ad2antrr.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "mpbir2and.mm"
include "ifeq1da.mm"
include "ifid.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "absid.mm"
include "3eqtr4d.mm"
include "negcld.mm"
include "addid2d.mm"
include "mpan2.mm"
include "biimprd.mm"
include "impl.mm"
include "le0neg1.mm"
include "iftrued.mm"
include "absnid.mm"
include "lecasei.mm"

theorem max0add
  let cA: class A


  assert |- ( A e. RR -> ( if ( 0 <_ A , A , 0 ) + if ( 0 <_ -u A , -u A , 0 ) ) = ( abs ` A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cc0
    cif
    #
    cc0
    cA
    cneg
    #
    cle
    wbr
    #
    @3
    cc0
    cif
    #
    caddc
    co
    #
    cA
    cabs
    cfv
    #
    wceq
    cc0
    cA
    @0
    0red
    @0
    id
    @0
    @1
    wa
    #
    cA
    cc0
    caddc
    co
    cA
    @6
    @7
    @8
    cA
    @0
    cA
    cc
    wcel
    #
    @1
    cA
    recn
    #
    adantr
    addid1d
    @8
    @2
    cA
    @5
    cc0
    caddc
    @1
    @2
    cA
    wceq
    @0
    @1
    cA
    cc0
    iftrue
    adantl
    @8
    @5
    @4
    cc0
    cc0
    cif
    cc0
    @8
    @4
    @3
    cc0
    cc0
    @8
    @4
    wa
    #
    @3
    cc0
    wceq
    #
    @3
    cc0
    cle
    wbr
    #
    @4
    @8
    @13
    @4
    @0
    @1
    @13
    cA
    le0neg2
    biimpa
    adantr
    @8
    @4
    simpr
    @11
    @3
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @12
    @13
    @4
    wa
    wb
    @0
    @14
    @1
    @4
    cA
    renegcl
    ad2antrr
    0re
    @3
    cc0
    letri3
    sylancl
    mpbir2and
    ifeq1da
    @4
    cc0
    ifid
    syl6eq
    oveq12d
    cA
    absid
    3eqtr4d
    @0
    cA
    cc0
    cle
    wbr
    #
    wa
    #
    cc0
    @3
    caddc
    co
    @3
    @6
    @7
    @17
    @3
    @17
    cA
    @0
    @9
    @16
    @10
    adantr
    negcld
    addid2d
    @17
    @2
    cc0
    @5
    @3
    caddc
    @17
    @2
    @1
    cc0
    cc0
    cif
    cc0
    @17
    @1
    cA
    cc0
    cc0
    @0
    @16
    @1
    cA
    cc0
    wceq
    #
    @0
    @18
    @16
    @1
    wa
    #
    @0
    @15
    @18
    @19
    wb
    0re
    cA
    cc0
    letri3
    mpan2
    biimprd
    impl
    ifeq1da
    @1
    cc0
    ifid
    syl6eq
    @17
    @4
    @3
    cc0
    @0
    @16
    @4
    cA
    le0neg1
    biimpa
    iftrued
    oveq12d
    cA
    absnid
    3eqtr4d
    lecasei
end

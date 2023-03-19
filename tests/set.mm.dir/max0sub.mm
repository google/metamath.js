include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "0red.mm"
include "id.mm"
include "wa.mm"
include "iftrue.mm"
include "adantl.mm"
include "cxr.mm"
include "0xr.mm"
include "a1i.mm"
include "renegcl.mm"
include "adantr.mm"
include "rexrd.mm"
include "le0neg2.mm"
include "biimpa.mm"
include "xrmaxeq.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "cc.mm"
include "recn.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "rexr.mm"
include "simpr.mm"
include "le0neg1.mm"
include "iftrued.mm"
include "df-neg.mm"
include "negnegd.mm"
include "syl5eqr.mm"
include "lecasei.mm"

theorem max0sub
  let cA: class A


  assert |- ( A e. RR -> ( if ( 0 <_ A , A , 0 ) - if ( 0 <_ -u A , -u A , 0 ) ) = A )

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
    cmin
    co
    #
    cA
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
    @6
    cA
    cc0
    cmin
    co
    cA
    @7
    @2
    cA
    @5
    cc0
    cmin
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
    @7
    cc0
    cxr
    wcel
    #
    @3
    cxr
    wcel
    @3
    cc0
    cle
    wbr
    #
    @5
    cc0
    wceq
    @8
    @7
    0xr
    a1i
    @7
    @3
    @0
    @3
    cr
    wcel
    @1
    cA
    renegcl
    adantr
    rexrd
    @0
    @1
    @9
    cA
    le0neg2
    biimpa
    cc0
    @3
    xrmaxeq
    syl3anc
    oveq12d
    @7
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
    subid1d
    eqtrd
    @0
    cA
    cc0
    cle
    wbr
    #
    wa
    #
    @6
    cc0
    @3
    cmin
    co
    #
    cA
    @13
    @2
    cc0
    @5
    @3
    cmin
    @13
    @8
    cA
    cxr
    wcel
    #
    @12
    @2
    cc0
    wceq
    @8
    @13
    0xr
    a1i
    @0
    @15
    @12
    cA
    rexr
    adantr
    @0
    @12
    simpr
    cc0
    cA
    xrmaxeq
    syl3anc
    @13
    @4
    @3
    cc0
    @0
    @12
    @4
    cA
    le0neg1
    biimpa
    iftrued
    oveq12d
    @13
    @14
    @3
    cneg
    cA
    @3
    df-neg
    @13
    cA
    @0
    @10
    @12
    @11
    adantr
    negnegd
    syl5eqr
    eqtrd
    lecasei
end

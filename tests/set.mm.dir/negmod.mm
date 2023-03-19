include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cmo.mm"
include "cneg.mm"
include "caddc.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "rpcn.mm"
include "recn.mm"
include "negsub.mm"
include "syl2anr.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "adantl.mm"
include "1cnd.mm"
include "mulcl.mm"
include "syl2an.mm"
include "renegcl.mm"
include "recnd.mm"
include "adantr.mm"
include "addcomd.mm"
include "cz.mm"
include "simpr.mm"
include "1zzd.mm"
include "modcyc.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "3eqtr2rd.mm"

theorem negmod
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. RR+ ) -> ( -u A mod N ) = ( ( N - A ) mod N ) )

  proof
    cA
    cr
    wcel
    #
    cN
    crp
    wcel
    #
    wa
    #
    cN
    cA
    cmin
    co
    #
    cN
    cmo
    co
    cN
    cA
    cneg
    #
    caddc
    co
    #
    cN
    cmo
    co
    c1
    cN
    cmul
    co
    #
    @4
    caddc
    co
    #
    cN
    cmo
    co
    #
    @4
    cN
    cmo
    co
    #
    @2
    @3
    @5
    cN
    cmo
    @2
    @5
    @3
    @1
    cN
    cc
    wcel
    #
    cA
    cc
    wcel
    @5
    @3
    wceq
    @0
    cN
    rpcn
    #
    cA
    recn
    cN
    cA
    negsub
    syl2anr
    eqcomd
    oveq1d
    @2
    @7
    @5
    cN
    cmo
    @2
    @6
    cN
    @4
    caddc
    @1
    @6
    cN
    wceq
    @0
    @1
    cN
    @11
    mulid2d
    adantl
    oveq1d
    oveq1d
    @2
    @8
    @4
    @6
    caddc
    co
    #
    cN
    cmo
    co
    #
    @9
    @2
    @7
    @12
    cN
    cmo
    @2
    @6
    @4
    @0
    c1
    cc
    wcel
    @10
    @6
    cc
    wcel
    @1
    @0
    1cnd
    @11
    c1
    cN
    mulcl
    syl2an
    @0
    @4
    cc
    wcel
    @1
    @0
    @4
    cA
    renegcl
    #
    recnd
    adantr
    addcomd
    oveq1d
    @2
    @4
    cr
    wcel
    #
    @1
    c1
    cz
    wcel
    @13
    @9
    wceq
    @0
    @15
    @1
    @14
    adantr
    @0
    @1
    simpr
    @2
    1zzd
    @4
    cN
    c1
    modcyc
    syl3anc
    eqtrd
    3eqtr2rd
end

include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "cr.mm"
include "nnre.mm"
include "3ad2ant1.mm"
include "wne.mm"
include "nnne0.mm"
include "sqgt0d.mm"
include "resqcld.mm"
include "3ad2ant2.mm"
include "ltaddpos2d.mm"
include "mpbid.mm"
include "adantr.mm"
include "simpr.mm"
include "breqtrd.mm"
include "3ad2ant3.mm"
include "cle.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "lt2sqd.mm"
include "mpbird.mm"
include "posdifd.mm"

theorem pythagtriplem10
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. NN /\ B e. NN /\ C e. NN ) /\ ( ( A ^ 2 ) + ( B ^ 2 ) ) = ( C ^ 2 ) ) -> 0 < ( C - B ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    caddc
    co
    #
    cC
    c2
    cexp
    co
    #
    wceq
    #
    wa
    #
    cB
    cC
    clt
    wbr
    #
    cc0
    cC
    cB
    cmin
    co
    clt
    wbr
    @9
    @10
    @5
    @7
    clt
    wbr
    @9
    @5
    @6
    @7
    clt
    @3
    @5
    @6
    clt
    wbr
    #
    @8
    @3
    cc0
    @4
    clt
    wbr
    @11
    @3
    cA
    @0
    @1
    cA
    cr
    wcel
    @2
    cA
    nnre
    3ad2ant1
    #
    @0
    @1
    cA
    cc0
    wne
    @2
    cA
    nnne0
    3ad2ant1
    sqgt0d
    @3
    @4
    @5
    @3
    cA
    @12
    resqcld
    @3
    cB
    @1
    @0
    cB
    cr
    wcel
    #
    @2
    cB
    nnre
    3ad2ant2
    #
    resqcld
    ltaddpos2d
    mpbid
    adantr
    @3
    @8
    simpr
    breqtrd
    @9
    cB
    cC
    @3
    @13
    @8
    @14
    adantr
    #
    @3
    cC
    cr
    wcel
    #
    @8
    @2
    @0
    @16
    @1
    cC
    nnre
    3ad2ant3
    adantr
    #
    @3
    cc0
    cB
    cle
    wbr
    #
    @8
    @1
    @0
    @18
    @2
    @1
    cB
    cB
    nnnn0
    nn0ge0d
    3ad2ant2
    adantr
    @3
    cc0
    cC
    cle
    wbr
    #
    @8
    @2
    @0
    @19
    @1
    @2
    cC
    cC
    nnnn0
    nn0ge0d
    3ad2ant3
    adantr
    lt2sqd
    mpbird
    @9
    cB
    cC
    @15
    @17
    posdifd
    mpbid
end

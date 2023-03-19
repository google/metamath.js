include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cneg.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "eldmgm.mm"
include "simprbi.mm"
include "adantr.mm"
include "wceq.mm"
include "cmin.mm"
include "df-neg.mm"
include "eqeq1i.mm"
include "0cnd.mm"
include "eldifi.mm"
include "nn0cn.mm"
include "adantl.mm"
include "subaddd.mm"
include "syl5bb.mm"
include "simpr.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "sylbird.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem dmgmaddn0
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( CC \ ( ZZ \ NN ) ) /\ N e. NN0 ) -> ( A + N ) =/= 0 )

  proof
    cA
    cc
    cz
    cn
    cdif
    #
    cdif
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cneg
    #
    cn0
    wcel
    #
    wn
    #
    cA
    cN
    caddc
    co
    #
    cc0
    wne
    @1
    @6
    @2
    @1
    cA
    cc
    wcel
    #
    @6
    cA
    eldmgm
    simprbi
    adantr
    @3
    @5
    @7
    cc0
    @3
    @7
    cc0
    wceq
    #
    @4
    cN
    wceq
    #
    @5
    @10
    cc0
    cA
    cmin
    co
    #
    cN
    wceq
    @3
    @9
    @4
    @11
    cN
    cA
    df-neg
    eqeq1i
    @3
    cc0
    cA
    cN
    @3
    0cnd
    @1
    @8
    @2
    cA
    cc
    @0
    eldifi
    adantr
    @2
    cN
    cc
    wcel
    @1
    cN
    nn0cn
    adantl
    subaddd
    syl5bb
    @3
    @5
    @10
    @2
    @1
    @2
    simpr
    @4
    cN
    cn0
    eleq1
    syl5ibrcom
    sylbird
    necon3bd
    mpd
end

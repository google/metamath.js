include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cprime.mm"
include "w3a.mm"
include "cv.mm"
include "cn0.mm"
include "wrex.mm"
include "cfmtno.mm"
include "cfv.mm"
include "simp1.mm"
include "eleq1.mm"
include "biimpa.mm"
include "3adant1.mm"
include "2pwp1prm.mm"
include "syl2anc.mm"
include "wi.mm"
include "wa.mm"
include "simpl.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "adantl.mm"
include "eqtrd.mm"
include "fmtno.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "exp32.mm"
include "com12.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "reximdva.mm"
include "mpd.mm"

theorem 2pwp1prmfmtno
  let cP: class P
  let vn: setvar n
  let cK: class K
  let vk: setvar k
  let vx: setvar x

  disjoint K n
  disjoint P n
  disjoint k x
  assert |- ( ( K e. NN /\ P = ( ( 2 ^ K ) + 1 ) /\ P e. Prime ) -> E. n e. NN0 P = ( FermatNo ` n ) )

  proof
    cK
    cn
    wcel
    #
    cP
    c2
    cK
    cexp
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    cP
    cprime
    wcel
    #
    w3a
    #
    cK
    c2
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    cP
    @6
    cfmtno
    cfv
    #
    wceq
    #
    vn
    cn0
    wrex
    @5
    @0
    @2
    cprime
    wcel
    #
    @9
    @0
    @3
    @4
    simp1
    @3
    @4
    @12
    @0
    @3
    @4
    @12
    cP
    @2
    cprime
    eleq1
    biimpa
    3adant1
    vn
    cK
    2pwp1prm
    syl2anc
    @5
    @8
    @11
    vn
    cn0
    @5
    @6
    cn0
    wcel
    #
    @8
    @11
    wi
    #
    @3
    @0
    @13
    @14
    wi
    @4
    @13
    @3
    @14
    @13
    @3
    @8
    @11
    @3
    @8
    wa
    #
    @13
    cP
    c2
    @7
    cexp
    co
    #
    c1
    caddc
    co
    #
    @10
    @15
    cP
    @2
    @17
    @3
    @8
    simpl
    @8
    @2
    @17
    wceq
    @3
    @8
    @1
    @16
    c1
    caddc
    cK
    @7
    c2
    cexp
    oveq2
    oveq1d
    adantl
    eqtrd
    @13
    @10
    @17
    @6
    fmtno
    eqcomd
    sylan9eqr
    exp32
    com12
    3ad2ant2
    imp
    reximdva
    mpd
end

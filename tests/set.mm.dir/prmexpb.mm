include "cprime.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cdvds.mm"
include "wbr.mm"
include "cz.mm"
include "prmz.mm"
include "adantr.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "iddvdsexp.mm"
include "syl2anc.mm"
include "wb.mm"
include "breq2.mm"
include "3ad2ant3.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2r.mm"
include "prmdvdsexpb.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "mpbid.mm"
include "zred.mm"
include "nnzd.mm"
include "c1.mm"
include "clt.mm"
include "prmgt1.mm"
include "ad2antrr.mm"
include "3adant3.mm"
include "simp3.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "expcand.mm"
include "jca.mm"
include "3expia.mm"
include "oveq12.mm"
include "impbid1.mm"

theorem prmexpb
  let cP: class P
  let cQ: class Q
  let cM: class M
  let cN: class N


  assert |- ( ( ( P e. Prime /\ Q e. Prime ) /\ ( M e. NN /\ N e. NN ) ) -> ( ( P ^ M ) = ( Q ^ N ) <-> ( P = Q /\ M = N ) ) )

  proof
    cP
    cprime
    wcel
    #
    cQ
    cprime
    wcel
    #
    wa
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    wa
    cP
    cM
    cexp
    co
    #
    cQ
    cN
    cexp
    co
    #
    wceq
    #
    cP
    cQ
    wceq
    #
    cM
    cN
    wceq
    #
    wa
    #
    @2
    @5
    @8
    @11
    @2
    @5
    @8
    w3a
    #
    @9
    @10
    @12
    cP
    @6
    cdvds
    wbr
    #
    @9
    @12
    cP
    cz
    wcel
    #
    @3
    @13
    @2
    @5
    @14
    @8
    @0
    @14
    @1
    cP
    prmz
    adantr
    3ad2ant1
    #
    @2
    @3
    @4
    @8
    simp2l
    #
    cP
    cM
    iddvdsexp
    syl2anc
    @12
    @13
    cP
    @7
    cdvds
    wbr
    #
    @9
    @8
    @2
    @13
    @17
    wb
    @5
    @6
    @7
    cP
    cdvds
    breq2
    3ad2ant3
    @12
    @0
    @1
    @4
    @17
    @9
    wb
    @0
    @1
    @5
    @8
    simp1l
    @0
    @1
    @5
    @8
    simp1r
    @2
    @3
    @4
    @8
    simp2r
    #
    cP
    cQ
    cN
    prmdvdsexpb
    syl3anc
    bitrd
    mpbid
    #
    @12
    cP
    cM
    cN
    @12
    cP
    @15
    zred
    @12
    cM
    @16
    nnzd
    @12
    cN
    @18
    nnzd
    @2
    @5
    c1
    cP
    clt
    wbr
    #
    @8
    @0
    @20
    @1
    @5
    cP
    prmgt1
    ad2antrr
    3adant3
    @12
    @6
    @7
    cP
    cN
    cexp
    co
    @2
    @5
    @8
    simp3
    @12
    cP
    cQ
    cN
    cexp
    @19
    oveq1d
    eqtr4d
    expcand
    jca
    3expia
    cP
    cQ
    cM
    cN
    cexp
    oveq12
    impbid1
end

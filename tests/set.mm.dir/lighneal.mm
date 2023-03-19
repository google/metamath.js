include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wne.mm"
include "lighneallem1.mm"
include "eqneqall.mm"
include "syl5com.mm"
include "3exp.mm"
include "a1d.mm"
include "csn.mm"
include "cdif.mm"
include "eldifsn.mm"
include "cdvds.mm"
include "wbr.mm"
include "lighneallem2.mm"
include "com3r.mm"
include "com24.mm"
include "wn.mm"
include "lighneallem3.mm"
include "com14.mm"
include "expcomd.mm"
include "lighneallem4.mm"
include "pm2.61d.mm"
include "com13.mm"
include "sylbir.mm"
include "expcom.mm"
include "pm2.61ine.mm"
include "3imp1.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "adantl.mm"
include "cc.mm"
include "prmnn.mm"
include "nncnd.mm"
include "3ad2ant1.mm"
include "exp1d.mm"
include "cz.mm"
include "nnz.mm"
include "3ad2ant3.mm"
include "simpl1.mm"
include "eleq1.mm"
include "mpbird.mm"
include "mersenne.mm"
include "syl2an2r.mm"
include "ex.mm"
include "sylbid.mm"
include "adantr.mm"
include "impancom.mm"
include "jcai.mm"

theorem lighneal
  let cP: class P
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( P e. Prime /\ M e. NN /\ N e. NN ) /\ ( ( 2 ^ N ) - 1 ) = ( P ^ M ) ) -> ( M = 1 /\ N e. Prime ) )

  proof
    cP
    cprime
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    c2
    cN
    cexp
    co
    c1
    cmin
    co
    #
    cP
    cM
    cexp
    co
    #
    wceq
    #
    wa
    cM
    c1
    wceq
    #
    cN
    cprime
    wcel
    #
    @0
    @1
    @2
    @6
    @7
    @0
    @1
    @2
    @6
    @7
    wi
    #
    wi
    wi
    #
    wi
    cP
    c2
    cP
    c2
    wceq
    #
    @10
    @0
    @11
    @1
    @2
    @9
    @11
    @1
    @2
    w3a
    @4
    @5
    wne
    @6
    @7
    cP
    cM
    cN
    lighneallem1
    @7
    @4
    @5
    eqneqall
    syl5com
    3exp
    a1d
    @0
    cP
    c2
    wne
    #
    @10
    @0
    @12
    wa
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    @10
    cP
    cprime
    c2
    eldifsn
    @2
    @1
    @13
    @9
    @2
    c2
    cN
    cdvds
    wbr
    #
    @1
    @13
    @9
    wi
    #
    wi
    @2
    @13
    @1
    @14
    @9
    @13
    @1
    @2
    @14
    @9
    wi
    #
    @13
    @1
    @2
    @16
    @13
    @1
    @2
    w3a
    #
    @14
    @6
    @7
    cP
    cM
    cN
    lighneallem2
    3exp
    3exp
    com3r
    com24
    @1
    @14
    wn
    #
    @2
    @15
    @1
    c2
    cM
    cdvds
    wbr
    #
    @18
    @2
    @15
    wi
    #
    wi
    @1
    @18
    @19
    @20
    @13
    @18
    @19
    wa
    #
    @2
    @1
    @9
    @13
    @1
    @2
    @21
    @9
    @13
    @1
    @2
    @21
    @9
    wi
    @17
    @21
    @6
    @7
    cP
    cM
    cN
    lighneallem3
    3exp
    3exp
    com24
    com14
    expcomd
    @1
    @18
    @19
    wn
    #
    @20
    @13
    @18
    @22
    wa
    #
    @2
    @1
    @9
    @13
    @1
    @2
    @23
    @9
    @13
    @1
    @2
    @23
    @9
    wi
    @17
    @23
    @6
    @7
    cP
    cM
    cN
    lighneallem4
    3exp
    3exp
    com24
    com14
    expcomd
    pm2.61d
    com13
    pm2.61d
    com13
    sylbir
    expcom
    pm2.61ine
    3imp1
    @3
    @7
    @6
    @8
    @3
    @7
    wa
    @6
    @4
    cP
    c1
    cexp
    co
    #
    wceq
    #
    @8
    @7
    @6
    @25
    wb
    @3
    @7
    @5
    @24
    @4
    cM
    c1
    cP
    cexp
    oveq2
    eqeq2d
    adantl
    @3
    @25
    @8
    wi
    @7
    @3
    @25
    @4
    cP
    wceq
    #
    @8
    @3
    @24
    cP
    @4
    @3
    cP
    @0
    @1
    cP
    cc
    wcel
    @2
    @0
    cP
    cP
    prmnn
    nncnd
    3ad2ant1
    exp1d
    eqeq2d
    @3
    @26
    @8
    @3
    cN
    cz
    wcel
    #
    @26
    @4
    cprime
    wcel
    #
    @8
    @2
    @0
    @27
    @1
    cN
    nnz
    3ad2ant3
    @3
    @26
    wa
    @28
    @0
    @0
    @1
    @2
    @26
    simpl1
    @26
    @28
    @0
    wb
    @3
    @4
    cP
    cprime
    eleq1
    adantl
    mpbird
    cN
    mersenne
    syl2an2r
    ex
    sylbid
    adantr
    sylbid
    impancom
    jcai
end

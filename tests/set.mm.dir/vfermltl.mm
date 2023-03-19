include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmo.mm"
include "cphi.mm"
include "cfv.mm"
include "wceq.mm"
include "phiprm.mm"
include "eqcomd.mm"
include "3ad2ant1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cn.mm"
include "cgcd.mm"
include "prmnn.mm"
include "simp2.mm"
include "wa.mm"
include "prmz.mm"
include "anim1i.mm"
include "ancomd.mm"
include "3adant3.mm"
include "gcdcom.mm"
include "syl.mm"
include "coprm.mm"
include "biimp3a.mm"
include "eqtrd.mm"
include "eulerth.mm"
include "syl3anc.mm"
include "cr.mm"
include "clt.mm"
include "nnred.mm"
include "prmgt1.mm"
include "jca.mm"
include "1mod.mm"
include "3eqtrd.mm"

theorem vfermltl
  let cA: class A
  let cP: class P


  assert |- ( ( P e. Prime /\ A e. ZZ /\ -. P || A ) -> ( ( A ^ ( P - 1 ) ) mod P ) = 1 )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cP
    cA
    cdvds
    wbr
    wn
    #
    w3a
    #
    cA
    cP
    c1
    cmin
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    cA
    cP
    cphi
    cfv
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    c1
    cP
    cmo
    co
    #
    c1
    @3
    @5
    @7
    cP
    cmo
    @3
    @4
    @6
    cA
    cexp
    @0
    @1
    @4
    @6
    wceq
    @2
    @0
    @6
    @4
    cP
    phiprm
    eqcomd
    3ad2ant1
    oveq2d
    oveq1d
    @3
    cP
    cn
    wcel
    #
    @1
    cA
    cP
    cgcd
    co
    #
    c1
    wceq
    @8
    @9
    wceq
    @0
    @1
    @10
    @2
    cP
    prmnn
    #
    3ad2ant1
    @0
    @1
    @2
    simp2
    @3
    @11
    cP
    cA
    cgcd
    co
    #
    c1
    @3
    @1
    cP
    cz
    wcel
    #
    wa
    #
    @11
    @13
    wceq
    @0
    @1
    @15
    @2
    @0
    @1
    wa
    @14
    @1
    @0
    @14
    @1
    cP
    prmz
    anim1i
    ancomd
    3adant3
    cA
    cP
    gcdcom
    syl
    @0
    @1
    @2
    @13
    c1
    wceq
    cP
    cA
    coprm
    biimp3a
    eqtrd
    cA
    cP
    eulerth
    syl3anc
    @3
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    wa
    #
    @9
    c1
    wceq
    @0
    @1
    @18
    @2
    @0
    @16
    @17
    @0
    cP
    @12
    nnred
    cP
    prmgt1
    jca
    3ad2ant1
    cP
    1mod
    syl
    3eqtrd
end

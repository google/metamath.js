include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "1z.mm"
include "wne.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "nnuz.mm"
include "1zzd.mm"
include "climcl.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "subcld.mm"
include "simp3.mm"
include "subne0d.mm"
include "absrpcld.mm"
include "rphalfcld.mm"
include "eqidd.mm"
include "simp1.mm"
include "climi.mm"
include "simp2.mm"
include "rexanuz2.mm"
include "sylanbrc.mm"
include "wi.mm"
include "c0.mm"
include "nnz.mm"
include "uzid.mm"
include "ne0i.mm"
include "r19.2z.mm"
include "ex.mm"
include "4syl.mm"
include "simpr.mm"
include "simpll.mm"
include "abssubd.mm"
include "breq1d.mm"
include "cr.mm"
include "simplr.mm"
include "subcl.mm"
include "adantr.mm"
include "abscld.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "ltnrd.mm"
include "pm2.21d.mm"
include "syld.mm"
include "expd.mm"
include "sylbid.mm"
include "impr.mm"
include "adantld.mm"
include "expimpd.mm"
include "rexlimdvw.mm"
include "sylan9r.mm"
include "rexlimdva.mm"
include "syl2anc.mm"
include "mpd.mm"
include "3expia.mm"
include "necon4ad.mm"
include "mpi.mm"

theorem climuni
  let cA: class A
  let cB: class B
  let cF: class F
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( F ~~> A /\ F ~~> B ) -> A = B )

  proof
    cF
    cA
    cli
    wbr
    #
    cF
    cB
    cli
    wbr
    #
    wa
    #
    c1
    cz
    wcel
    #
    cA
    cB
    wceq
    1z
    @2
    @3
    cA
    cB
    @0
    @1
    cA
    cB
    wne
    #
    @3
    wn
    #
    @0
    @1
    @4
    w3a
    #
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @8
    cA
    cmin
    co
    cabs
    cfv
    #
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    wa
    #
    @9
    @8
    cB
    cmin
    co
    cabs
    cfv
    @13
    clt
    wbr
    #
    wa
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    @5
    @6
    @15
    vk
    @20
    wral
    vj
    cn
    wrex
    @17
    vk
    @20
    wral
    vj
    cn
    wrex
    @22
    @6
    cA
    @8
    @13
    vj
    vk
    cF
    c1
    cn
    nnuz
    @6
    1zzd
    #
    @6
    @12
    @6
    @11
    @6
    cA
    cB
    @0
    @1
    cA
    cc
    wcel
    #
    @4
    cA
    cF
    climcl
    3ad2ant1
    #
    @1
    @0
    cB
    cc
    wcel
    #
    @4
    cB
    cF
    climcl
    3ad2ant2
    #
    subcld
    @6
    cA
    cB
    @25
    @27
    @0
    @1
    @4
    simp3
    subne0d
    absrpcld
    rphalfcld
    #
    @6
    @7
    cn
    wcel
    wa
    @8
    eqidd
    #
    @0
    @1
    @4
    simp1
    climi
    @6
    cB
    @8
    @13
    vj
    vk
    cF
    c1
    cn
    nnuz
    @23
    @28
    @29
    @0
    @1
    @4
    simp2
    climi
    @15
    @17
    vj
    vk
    c1
    cn
    nnuz
    rexanuz2
    sylanbrc
    @6
    @24
    @26
    @22
    @5
    wi
    @25
    @27
    @24
    @26
    wa
    #
    @21
    @5
    vj
    cn
    @19
    cn
    wcel
    #
    @21
    @18
    vk
    @20
    wrex
    #
    @30
    @5
    @31
    @19
    cz
    wcel
    @19
    @20
    wcel
    @20
    c0
    wne
    #
    @21
    @32
    wi
    @19
    nnz
    @19
    uzid
    @20
    @19
    ne0i
    @33
    @21
    @32
    @18
    vk
    @20
    r19.2z
    ex
    4syl
    @30
    @18
    @5
    vk
    @20
    @30
    @15
    @17
    @5
    @30
    @15
    wa
    @16
    @5
    @9
    @30
    @9
    @14
    @16
    @5
    wi
    #
    @30
    @9
    wa
    #
    @14
    cA
    @8
    cmin
    co
    cabs
    cfv
    #
    @13
    clt
    wbr
    #
    @34
    @35
    @10
    @36
    @13
    clt
    @35
    @8
    cA
    @30
    @9
    simpr
    #
    @24
    @26
    @9
    simpll
    #
    abssubd
    breq1d
    @35
    @37
    @16
    @5
    @35
    @37
    @16
    wa
    #
    @12
    @12
    clt
    wbr
    #
    @5
    @35
    @24
    @26
    @9
    @12
    cr
    wcel
    @40
    @41
    wi
    @39
    @24
    @26
    @9
    simplr
    @38
    @35
    @11
    @30
    @11
    cc
    wcel
    @9
    cA
    cB
    subcl
    adantr
    abscld
    #
    cA
    cB
    @8
    @12
    abs3lem
    syl22anc
    @35
    @41
    @5
    @35
    @12
    @42
    ltnrd
    pm2.21d
    syld
    expd
    sylbid
    impr
    adantld
    expimpd
    rexlimdvw
    sylan9r
    rexlimdva
    syl2anc
    mpd
    3expia
    necon4ad
    mpi
end

include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cpellfund.mm"
include "csqrt.mm"
include "caddc.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "cpell14qr.mm"
include "clt.mm"
include "rmspecnonsq.mm"
include "cmul.mm"
include "cz.mm"
include "eluzelz.mm"
include "zsqcl.mm"
include "syl.mm"
include "zred.mm"
include "1red.mm"
include "resubcld.mm"
include "cc0.mm"
include "sq1.mm"
include "a1i.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "eluzelre.mm"
include "0le1.mm"
include "eluzge2nn0.mm"
include "nn0ge0d.mm"
include "lt2sqd.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "posdifd.mm"
include "elrpd.mm"
include "rpsqrtcld.mm"
include "rpred.mm"
include "recnd.mm"
include "mulid1d.mm"
include "oveq2d.mm"
include "cpell1qr.mm"
include "wss.mm"
include "pell1qrss14.mm"
include "cn0.mm"
include "1nn0.mm"
include "oveq2i.mm"
include "syl5eq.mm"
include "1cnd.mm"
include "nncand.mm"
include "eqtrd.mm"
include "pellqrexplicit.mm"
include "syl31anc.mm"
include "sseldd.mm"
include "eqeltrrd.mm"
include "readdcld.mm"
include "ltaddrpd.mm"
include "ltadd1dd.mm"
include "lttrd.mm"
include "pellfundlb.mm"
include "syl3anc.mm"
include "npcand.mm"
include "fveq2d.mm"
include "sqrtsqd.mm"
include "oveq1d.mm"
include "pellfundge.mm"
include "cr.mm"
include "pellfundre.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem rmspecfund
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( PellFund ` ( ( A ^ 2 ) - 1 ) ) = ( A + ( sqrt ` ( ( A ^ 2 ) - 1 ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    cA
    c2
    cexp
    co
    #
    c1
    cmin
    co
    #
    cpellfund
    cfv
    #
    cA
    @2
    csqrt
    cfv
    #
    caddc
    co
    #
    wceq
    @3
    @5
    cle
    wbr
    #
    @5
    @3
    cle
    wbr
    @0
    @2
    cn
    csquarenn
    cdif
    wcel
    #
    @5
    @2
    cpell14qr
    cfv
    #
    wcel
    c1
    @5
    clt
    wbr
    @6
    cA
    rmspecnonsq
    #
    @0
    cA
    @4
    c1
    cmul
    co
    #
    caddc
    co
    #
    @5
    @8
    @0
    @10
    @4
    cA
    caddc
    @0
    @4
    @0
    @4
    @0
    @4
    @0
    @2
    @0
    @2
    @0
    @1
    c1
    @0
    @1
    @0
    cA
    cz
    wcel
    @1
    cz
    wcel
    c2
    cA
    eluzelz
    cA
    zsqcl
    syl
    zred
    #
    @0
    1red
    #
    resubcld
    #
    @0
    c1
    @1
    clt
    wbr
    cc0
    @2
    clt
    wbr
    @0
    c1
    c2
    cexp
    co
    #
    c1
    @1
    clt
    @15
    c1
    wceq
    @0
    sq1
    a1i
    @0
    c1
    cA
    clt
    wbr
    #
    @15
    @1
    clt
    wbr
    @0
    cA
    cn
    wcel
    @16
    cA
    eluz2b2
    simprbi
    #
    @0
    c1
    cA
    @13
    c2
    cA
    eluzelre
    #
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    @0
    cA
    cA
    eluzge2nn0
    #
    nn0ge0d
    #
    lt2sqd
    mpbid
    eqbrtrrd
    @0
    c1
    @1
    @13
    @12
    posdifd
    mpbid
    elrpd
    rpsqrtcld
    #
    rpred
    #
    recnd
    mulid1d
    oveq2d
    @0
    @2
    cpell1qr
    cfv
    #
    @8
    @11
    @0
    @7
    @23
    @8
    wss
    @9
    @2
    pell1qrss14
    syl
    @0
    @7
    cA
    cn0
    wcel
    c1
    cn0
    wcel
    #
    @1
    @2
    @15
    cmul
    co
    #
    cmin
    co
    #
    c1
    wceq
    @11
    @23
    wcel
    @9
    @19
    @24
    @0
    1nn0
    a1i
    @0
    @26
    @1
    @2
    cmin
    co
    c1
    @0
    @25
    @2
    @1
    cmin
    @0
    @25
    @2
    c1
    cmul
    co
    @2
    @15
    c1
    @2
    cmul
    sq1
    oveq2i
    @0
    @2
    @0
    @2
    @14
    recnd
    mulid1d
    syl5eq
    oveq2d
    @0
    @1
    c1
    @0
    @1
    @12
    recnd
    #
    @0
    1cnd
    #
    nncand
    eqtrd
    cA
    c1
    @2
    pellqrexplicit
    syl31anc
    sseldd
    eqeltrrd
    @0
    c1
    c1
    @4
    caddc
    co
    @5
    @13
    @0
    c1
    @4
    @13
    @22
    readdcld
    @0
    cA
    @4
    @18
    @22
    readdcld
    #
    @0
    c1
    @4
    @13
    @21
    ltaddrpd
    @0
    c1
    cA
    @4
    @13
    @18
    @22
    @17
    ltadd1dd
    lttrd
    @5
    @2
    pellfundlb
    syl3anc
    @0
    @2
    c1
    caddc
    co
    #
    csqrt
    cfv
    #
    @4
    caddc
    co
    #
    @5
    @3
    cle
    @0
    @31
    cA
    @4
    caddc
    @0
    @31
    @1
    csqrt
    cfv
    cA
    @0
    @30
    @1
    csqrt
    @0
    @1
    c1
    @27
    @28
    npcand
    fveq2d
    @0
    cA
    @18
    @20
    sqrtsqd
    eqtrd
    oveq1d
    @0
    @7
    @32
    @3
    cle
    wbr
    @9
    @2
    pellfundge
    syl
    eqbrtrrd
    @0
    @3
    @5
    @0
    @7
    @3
    cr
    wcel
    @9
    @2
    pellfundre
    syl
    @29
    letri3d
    mpbir2and
end

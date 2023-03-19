include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cprime.mm"
include "wa.mm"
include "ccht.mm"
include "cfv.mm"
include "c2.mm"
include "cfz.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "csu.mm"
include "csn.mm"
include "cc0.mm"
include "cicc.mm"
include "cr.mm"
include "wceq.mm"
include "peano2z.mm"
include "adantr.mm"
include "zre.mm"
include "syl.mm"
include "chtval.mm"
include "cfl.mm"
include "ppisval.mm"
include "flid.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "eqtrd.mm"
include "sumeq1d.mm"
include "wn.mm"
include "c0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "ltp1d.mm"
include "ltnled.mm"
include "mpbid.mm"
include "inss1.mm"
include "sseli.mm"
include "elfzle2.mm"
include "nsyl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cun.mm"
include "cmin.mm"
include "cuz.mm"
include "2z.mm"
include "cn.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "prmuz2.mm"
include "adantl.mm"
include "uz2m1nn.mm"
include "eqeltrrd.mm"
include "nnuz.mm"
include "2m1e1.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "fzsuc2.mm"
include "sylancr.mm"
include "indir.mm"
include "syl6eq.mm"
include "wss.mm"
include "simpr.mm"
include "snssd.mm"
include "df-ss.mm"
include "sylib.mm"
include "uneq2d.mm"
include "cfn.mm"
include "fzfid.mm"
include "ssfi.mm"
include "inss2.mm"
include "sseldi.mm"
include "prmnn.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "recnd.mm"
include "fsumsplit.mm"
include "eqtr2d.mm"
include "fveq2.mm"
include "sumsn.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "3eqtrd.mm"

theorem chtprm
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- ( ( A e. ZZ /\ ( A + 1 ) e. Prime ) -> ( theta ` ( A + 1 ) ) = ( ( theta ` A ) + ( log ` ( A + 1 ) ) ) )

  proof
    cA
    cz
    wcel
    #
    cA
    c1
    caddc
    co
    #
    cprime
    wcel
    #
    wa
    #
    @1
    ccht
    cfv
    #
    c2
    @1
    cfz
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    vp
    csu
    #
    c2
    cA
    cfz
    co
    #
    cprime
    cin
    #
    @8
    vp
    csu
    #
    @1
    csn
    #
    @8
    vp
    csu
    #
    caddc
    co
    cA
    ccht
    cfv
    #
    @1
    clog
    cfv
    #
    caddc
    co
    @3
    @4
    cc0
    @1
    cicc
    co
    cprime
    cin
    #
    @8
    vp
    csu
    #
    @9
    @3
    @1
    cr
    wcel
    #
    @4
    @18
    wceq
    @3
    @1
    cz
    wcel
    #
    @19
    @0
    @20
    @2
    cA
    peano2z
    adantr
    #
    @1
    zre
    syl
    #
    @1
    vp
    chtval
    syl
    @3
    @17
    @6
    @8
    vp
    @3
    @17
    c2
    @1
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    @6
    @3
    @19
    @17
    @25
    wceq
    @22
    @1
    ppisval
    syl
    @3
    @24
    @5
    cprime
    @3
    @23
    @1
    c2
    cfz
    @3
    @20
    @23
    @1
    wceq
    @21
    @1
    flid
    syl
    oveq2d
    ineq1d
    eqtrd
    sumeq1d
    eqtrd
    @3
    @11
    @13
    @8
    @6
    vp
    @3
    @1
    @11
    wcel
    #
    wn
    @11
    @13
    cin
    c0
    wceq
    @3
    @1
    cA
    cle
    wbr
    #
    @26
    @3
    cA
    @1
    clt
    wbr
    @27
    wn
    @3
    cA
    @0
    cA
    cr
    wcel
    #
    @2
    cA
    zre
    adantr
    #
    ltp1d
    @3
    cA
    @1
    @29
    @22
    ltnled
    mpbid
    @26
    @1
    @10
    wcel
    @27
    @11
    @10
    @1
    @10
    cprime
    inss1
    sseli
    @1
    c2
    cA
    elfzle2
    syl
    nsyl
    @11
    @1
    disjsn
    sylibr
    @3
    @6
    @11
    @13
    cprime
    cin
    #
    cun
    #
    @11
    @13
    cun
    @3
    @6
    @10
    @13
    cun
    #
    cprime
    cin
    @31
    @3
    @5
    @32
    cprime
    @3
    c2
    cz
    wcel
    cA
    c2
    c1
    cmin
    co
    #
    cuz
    cfv
    #
    wcel
    @5
    @32
    wceq
    2z
    @3
    cA
    cn
    @34
    @3
    @1
    c1
    cmin
    co
    #
    cA
    cn
    @3
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    @35
    cA
    wceq
    @0
    @36
    @2
    cA
    zcn
    adantr
    ax-1cn
    cA
    c1
    pncan
    sylancl
    @3
    @1
    c2
    cuz
    cfv
    wcel
    #
    @35
    cn
    wcel
    @2
    @37
    @0
    @1
    prmuz2
    adantl
    @1
    uz2m1nn
    syl
    eqeltrrd
    cn
    c1
    cuz
    cfv
    @34
    nnuz
    @33
    c1
    cuz
    2m1e1
    fveq2i
    eqtr4i
    syl6eleq
    c2
    cA
    fzsuc2
    sylancr
    ineq1d
    @10
    @13
    cprime
    indir
    syl6eq
    @3
    @30
    @13
    @11
    @3
    @13
    cprime
    wss
    @30
    @13
    wceq
    @3
    @1
    cprime
    @0
    @2
    simpr
    snssd
    @13
    cprime
    df-ss
    sylib
    uneq2d
    eqtrd
    @3
    @5
    cfn
    wcel
    @6
    @5
    wss
    @6
    cfn
    wcel
    @3
    c2
    @1
    fzfid
    @5
    cprime
    inss1
    @5
    @6
    ssfi
    sylancl
    @3
    @7
    @6
    wcel
    #
    wa
    #
    @8
    @39
    @7
    @39
    @7
    @39
    @7
    cprime
    wcel
    @7
    cn
    wcel
    @39
    @6
    cprime
    @7
    @5
    cprime
    inss2
    @3
    @38
    simpr
    sseldi
    @7
    prmnn
    syl
    nnrpd
    relogcld
    recnd
    fsumsplit
    @3
    @12
    @15
    @14
    @16
    caddc
    @3
    @15
    cc0
    cA
    cicc
    co
    cprime
    cin
    #
    @8
    vp
    csu
    #
    @12
    @3
    @28
    @15
    @41
    wceq
    @29
    cA
    vp
    chtval
    syl
    @3
    @40
    @11
    @8
    vp
    @3
    @40
    c2
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    cprime
    cin
    #
    @11
    @3
    @28
    @40
    @44
    wceq
    @29
    cA
    ppisval
    syl
    @3
    @43
    @10
    cprime
    @3
    @42
    cA
    c2
    cfz
    @0
    @42
    cA
    wceq
    @2
    cA
    flid
    adantr
    oveq2d
    ineq1d
    eqtrd
    sumeq1d
    eqtr2d
    @3
    @1
    cn
    wcel
    #
    @16
    cc
    wcel
    @14
    @16
    wceq
    @2
    @45
    @0
    @1
    prmnn
    adantl
    #
    @3
    @16
    @3
    @1
    @3
    @1
    @46
    nnrpd
    relogcld
    recnd
    @8
    @16
    vp
    @1
    cn
    @7
    @1
    clog
    fveq2
    sumsn
    syl2anc
    oveq12d
    3eqtrd
end

include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cprime.mm"
include "wa.mm"
include "c2.mm"
include "cfz.mm"
include "cin.mm"
include "csn.mm"
include "cun.mm"
include "chash.mm"
include "cfv.mm"
include "cppi.mm"
include "cfn.mm"
include "wn.mm"
include "wceq.mm"
include "wss.mm"
include "fzfid.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cr.mm"
include "zre.mm"
include "adantr.mm"
include "ltp1d.mm"
include "peano2z.mm"
include "zred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "sseli.mm"
include "elfzle2.mm"
include "syl.mm"
include "nsyl.mm"
include "cvv.mm"
include "wi.mm"
include "ovex.mm"
include "hashunsng.mm"
include "ax-mp.mm"
include "syl2anc.mm"
include "ppival2.mm"
include "cmin.mm"
include "cuz.mm"
include "2z.mm"
include "cn.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "pncan.mm"
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
include "ineq1d.mm"
include "indir.mm"
include "syl6eq.mm"
include "simpr.mm"
include "snssd.mm"
include "df-ss.mm"
include "sylib.mm"
include "uneq2d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"

theorem ppiprm
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


  assert |- ( ( A e. ZZ /\ ( A + 1 ) e. Prime ) -> ( ppi ` ( A + 1 ) ) = ( ( ppi ` A ) + 1 ) )

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
    c2
    cA
    cfz
    co
    #
    cprime
    cin
    #
    @1
    csn
    #
    cun
    #
    chash
    cfv
    #
    @5
    chash
    cfv
    #
    c1
    caddc
    co
    #
    @1
    cppi
    cfv
    #
    cA
    cppi
    cfv
    #
    c1
    caddc
    co
    @3
    @5
    cfn
    wcel
    #
    @1
    @5
    wcel
    #
    wn
    #
    @8
    @10
    wceq
    #
    @3
    @4
    cfn
    wcel
    @5
    @4
    wss
    @13
    @3
    c2
    cA
    fzfid
    @4
    cprime
    inss1
    #
    @4
    @5
    ssfi
    sylancl
    @3
    @1
    cA
    cle
    wbr
    #
    @14
    @3
    cA
    @1
    clt
    wbr
    @18
    wn
    @3
    cA
    @0
    cA
    cr
    wcel
    @2
    cA
    zre
    adantr
    #
    ltp1d
    @3
    cA
    @1
    @19
    @3
    @1
    @0
    @1
    cz
    wcel
    #
    @2
    cA
    peano2z
    adantr
    #
    zred
    ltnled
    mpbid
    @14
    @1
    @4
    wcel
    @18
    @5
    @4
    @1
    @17
    sseli
    @1
    c2
    cA
    elfzle2
    syl
    nsyl
    @1
    cvv
    wcel
    @13
    @15
    wa
    @16
    wi
    cA
    c1
    caddc
    ovex
    @5
    @1
    cvv
    hashunsng
    ax-mp
    syl2anc
    @3
    @11
    c2
    @1
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    @8
    @3
    @20
    @11
    @24
    wceq
    @21
    @1
    ppival2
    syl
    @3
    @23
    @7
    chash
    @3
    @23
    @5
    @6
    cprime
    cin
    #
    cun
    #
    @7
    @3
    @23
    @4
    @6
    cun
    #
    cprime
    cin
    @26
    @3
    @22
    @27
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
    @22
    @27
    wceq
    2z
    @3
    cA
    cn
    @29
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
    @30
    cA
    wceq
    @0
    @31
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
    @30
    cn
    wcel
    @2
    @32
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
    @29
    nnuz
    @28
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
    @4
    @6
    cprime
    indir
    syl6eq
    @3
    @25
    @6
    @5
    @3
    @6
    cprime
    wss
    @25
    @6
    wceq
    @3
    @1
    cprime
    @0
    @2
    simpr
    snssd
    @6
    cprime
    df-ss
    sylib
    uneq2d
    eqtrd
    fveq2d
    eqtrd
    @3
    @12
    @9
    c1
    caddc
    @0
    @12
    @9
    wceq
    @2
    cA
    ppival2
    adantr
    oveq1d
    3eqtr4d
end

include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cprime.mm"
include "wn.mm"
include "wa.mm"
include "cc0.mm"
include "cicc.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "csu.mm"
include "ccht.mm"
include "c2.mm"
include "cfl.mm"
include "cfz.mm"
include "csn.mm"
include "wne.mm"
include "inss2.mm"
include "simprr.mm"
include "sseldi.mm"
include "simprl.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "sylibr.mm"
include "cun.mm"
include "wo.mm"
include "inss1.mm"
include "cmin.mm"
include "cuz.mm"
include "wceq.mm"
include "2z.mm"
include "cn.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "elfzuz2.mm"
include "uz2m1nn.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "nnuz.mm"
include "2m1e1.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "syl6eleq.mm"
include "fzsuc2.mm"
include "sylancr.mm"
include "eleqtrd.mm"
include "elun.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "elind.mm"
include "expr.mm"
include "ssrdv.mm"
include "wss.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzss2.mm"
include "ssrin.mm"
include "4syl.mm"
include "eqssd.mm"
include "peano2z.mm"
include "flid.mm"
include "syl.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "3eqtr4d.mm"
include "cr.mm"
include "zre.mm"
include "peano2re.mm"
include "ppisval.mm"
include "sumeq1d.mm"
include "chtval.mm"

theorem chtnprm
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


  assert |- ( ( A e. ZZ /\ -. ( A + 1 ) e. Prime ) -> ( theta ` ( A + 1 ) ) = ( theta ` A ) )

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
    wn
    #
    wa
    #
    cc0
    @1
    cicc
    co
    cprime
    cin
    #
    vp
    cv
    clog
    cfv
    #
    vp
    csu
    #
    cc0
    cA
    cicc
    co
    cprime
    cin
    #
    @5
    vp
    csu
    #
    @1
    ccht
    cfv
    #
    cA
    ccht
    cfv
    #
    @3
    @4
    @7
    @5
    vp
    @3
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
    @4
    @7
    @3
    c2
    @1
    cfz
    co
    #
    cprime
    cin
    #
    c2
    cA
    cfz
    co
    #
    cprime
    cin
    #
    @13
    @16
    @3
    @18
    @20
    @3
    vx
    @18
    @20
    @0
    @2
    vx
    cv
    #
    @18
    wcel
    #
    @21
    @20
    wcel
    @0
    @2
    @22
    wa
    #
    wa
    #
    @19
    cprime
    @21
    @24
    @21
    @19
    wcel
    #
    @21
    @1
    csn
    #
    wcel
    #
    @24
    @21
    @1
    wne
    #
    @27
    wn
    @24
    @21
    cprime
    wcel
    @2
    @28
    @24
    @18
    cprime
    @21
    @17
    cprime
    inss2
    @0
    @2
    @22
    simprr
    #
    sseldi
    #
    @0
    @2
    @22
    simprl
    @21
    @1
    cprime
    nelne2
    syl2anc
    @27
    @21
    @1
    vx
    @1
    velsn
    necon3bbii
    sylibr
    @24
    @25
    @27
    @24
    @21
    @19
    @26
    cun
    #
    wcel
    @25
    @27
    wo
    @24
    @21
    @17
    @31
    @24
    @18
    @17
    @21
    @17
    cprime
    inss1
    @29
    sseldi
    #
    @24
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
    @17
    @31
    wceq
    2z
    @24
    cA
    cn
    @34
    @24
    @1
    c1
    cmin
    co
    #
    cA
    cn
    @24
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
    @23
    cA
    zcn
    adantr
    ax-1cn
    cA
    c1
    pncan
    sylancl
    @24
    @21
    @17
    wcel
    @1
    c2
    cuz
    cfv
    wcel
    @35
    cn
    wcel
    @32
    @21
    c2
    @1
    elfzuz2
    @1
    uz2m1nn
    3syl
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
    eleqtrd
    @21
    @19
    @26
    elun
    sylib
    ord
    mt3d
    @30
    elind
    expr
    ssrdv
    @3
    cA
    cA
    cuz
    cfv
    #
    wcel
    #
    @1
    @37
    wcel
    @19
    @17
    wss
    @20
    @18
    wss
    @0
    @38
    @2
    cA
    uzid
    adantr
    cA
    cA
    peano2uz
    cA
    c2
    @1
    fzss2
    @19
    @17
    cprime
    ssrin
    4syl
    eqssd
    @3
    @12
    @17
    cprime
    @3
    @11
    @1
    c2
    cfz
    @3
    @1
    cz
    wcel
    #
    @11
    @1
    wceq
    @0
    @39
    @2
    cA
    peano2z
    adantr
    @1
    flid
    syl
    oveq2d
    ineq1d
    @3
    @15
    @19
    cprime
    @3
    @14
    cA
    c2
    cfz
    @0
    @14
    cA
    wceq
    @2
    cA
    flid
    adantr
    oveq2d
    ineq1d
    3eqtr4d
    @3
    cA
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @4
    @13
    wceq
    @0
    @40
    @2
    cA
    zre
    adantr
    #
    cA
    peano2re
    #
    @1
    ppisval
    3syl
    @3
    @40
    @7
    @16
    wceq
    @42
    cA
    ppisval
    syl
    3eqtr4d
    sumeq1d
    @3
    @40
    @41
    @9
    @6
    wceq
    @42
    @43
    @1
    vp
    chtval
    3syl
    @3
    @40
    @10
    @8
    wceq
    @42
    cA
    vp
    chtval
    syl
    3eqtr4d
end

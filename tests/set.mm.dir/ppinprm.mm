include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cprime.mm"
include "wn.mm"
include "wa.mm"
include "c2.mm"
include "cfz.mm"
include "cin.mm"
include "chash.mm"
include "cfv.mm"
include "cppi.mm"
include "cv.mm"
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
include "fveq2d.mm"
include "peano2z.mm"
include "ppival2.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem ppinprm
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


  assert |- ( ( A e. ZZ /\ -. ( A + 1 ) e. Prime ) -> ( ppi ` ( A + 1 ) ) = ( ppi ` A ) )

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
    c2
    cA
    cfz
    co
    #
    cprime
    cin
    #
    chash
    cfv
    #
    @1
    cppi
    cfv
    #
    cA
    cppi
    cfv
    #
    @3
    @5
    @8
    chash
    @3
    @5
    @8
    @3
    vx
    @5
    @8
    @0
    @2
    vx
    cv
    #
    @5
    wcel
    #
    @12
    @8
    wcel
    @0
    @2
    @13
    wa
    #
    wa
    #
    @7
    cprime
    @12
    @15
    @12
    @7
    wcel
    #
    @12
    @1
    csn
    #
    wcel
    #
    @15
    @12
    @1
    wne
    #
    @18
    wn
    @15
    @12
    cprime
    wcel
    @2
    @19
    @15
    @5
    cprime
    @12
    @4
    cprime
    inss2
    @0
    @2
    @13
    simprr
    #
    sseldi
    #
    @0
    @2
    @13
    simprl
    @12
    @1
    cprime
    nelne2
    syl2anc
    @18
    @12
    @1
    vx
    @1
    velsn
    necon3bbii
    sylibr
    @15
    @16
    @18
    @15
    @12
    @7
    @17
    cun
    #
    wcel
    @16
    @18
    wo
    @15
    @12
    @4
    @22
    @15
    @5
    @4
    @12
    @4
    cprime
    inss1
    @20
    sseldi
    #
    @15
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
    @4
    @22
    wceq
    2z
    @15
    cA
    cn
    @25
    @15
    @1
    c1
    cmin
    co
    #
    cA
    cn
    @15
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    @26
    cA
    wceq
    @0
    @27
    @14
    cA
    zcn
    adantr
    ax-1cn
    cA
    c1
    pncan
    sylancl
    @15
    @12
    @4
    wcel
    @1
    c2
    cuz
    cfv
    wcel
    @26
    cn
    wcel
    @23
    @12
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
    @25
    nnuz
    @24
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
    @12
    @7
    @17
    elun
    sylib
    ord
    mt3d
    @21
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
    @28
    wcel
    @7
    @4
    wss
    @8
    @5
    wss
    @0
    @29
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
    @7
    @4
    cprime
    ssrin
    4syl
    eqssd
    fveq2d
    @3
    @1
    cz
    wcel
    #
    @10
    @6
    wceq
    @0
    @30
    @2
    cA
    peano2z
    adantr
    @1
    ppival2
    syl
    @0
    @11
    @9
    wceq
    @2
    cA
    ppival2
    adantr
    3eqtr4d
end

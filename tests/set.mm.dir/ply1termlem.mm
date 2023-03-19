include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "simplr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "fzss1.mm"
include "syl.mm"
include "elfz1eq.mm"
include "adantl.mm"
include "iftrue.mm"
include "simpll.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "expcld.mm"
include "mulcld.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "cz.mm"
include "wb.mm"
include "nn0zd.mm"
include "csn.mm"
include "fzsn.mm"
include "eleq2d.mm"
include "elsn2g.mm"
include "bitrd.mm"
include "mtbid.mm"
include "iffalsed.mm"
include "oveq1d.mm"
include "simpr.mm"
include "eldifi.mm"
include "elfznn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "fsumss.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fsum1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "mpteq2dva.mm"
include "syl6reqr.mm"

theorem ply1termlem
  let vz: setvar z
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cS: class S
  assume ply1term.1: |- F = ( z e. CC |-> ( A x. ( z ^ N ) ) )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint N k
  disjoint N z
  disjoint S k
  disjoint S z
  assert |- ( ( A e. CC /\ N e. NN0 ) -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( if ( k = N , A , 0 ) x. ( z ^ k ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cN
    wceq
    #
    cA
    cc0
    cif
    #
    vz
    cv
    #
    @4
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    vz
    cc
    cA
    @7
    cN
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    cF
    @2
    vz
    cc
    @10
    @12
    @2
    @7
    cc
    wcel
    #
    wa
    #
    cN
    cN
    cfz
    co
    #
    @9
    vk
    csu
    #
    @10
    @12
    @14
    @15
    @3
    @9
    vk
    @14
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @15
    @3
    wss
    @14
    cN
    cn0
    @17
    @0
    @1
    @13
    simplr
    #
    nn0uz
    syl6eleq
    cN
    cc0
    cN
    fzss1
    syl
    @14
    @4
    @15
    wcel
    #
    wa
    #
    @6
    @8
    @20
    @6
    cA
    cc
    @20
    @5
    @6
    cA
    wceq
    @19
    @5
    @14
    @4
    cN
    elfz1eq
    adantl
    #
    @5
    cA
    cc0
    iftrue
    #
    syl
    @14
    @0
    @19
    @0
    @1
    @13
    simpll
    #
    adantr
    eqeltrd
    @20
    @7
    @4
    @2
    @13
    @19
    simplr
    @20
    @4
    cN
    cn0
    @21
    @14
    @1
    @19
    @18
    adantr
    eqeltrd
    expcld
    mulcld
    @14
    @4
    @3
    @15
    cdif
    wcel
    #
    wa
    #
    @9
    cc0
    @8
    cmul
    co
    cc0
    @25
    @6
    cc0
    @8
    cmul
    @25
    @5
    cA
    cc0
    @25
    @19
    @5
    @24
    @19
    wn
    @14
    @4
    @3
    @15
    eldifn
    adantl
    @25
    cN
    cz
    wcel
    #
    @19
    @5
    wb
    @25
    cN
    @14
    @1
    @24
    @18
    adantr
    nn0zd
    @26
    @19
    @4
    cN
    csn
    #
    wcel
    @5
    @26
    @15
    @27
    @4
    cN
    fzsn
    eleq2d
    @4
    cN
    cz
    elsn2g
    bitrd
    syl
    mtbid
    iffalsed
    oveq1d
    @25
    @8
    @14
    @13
    @4
    cn0
    wcel
    #
    @8
    cc
    wcel
    @24
    @2
    @13
    simpr
    #
    @24
    @4
    @3
    wcel
    @28
    @4
    @3
    @15
    eldifi
    @4
    cN
    elfznn0
    syl
    @7
    @4
    expcl
    syl2an
    mul02d
    eqtrd
    @14
    cc0
    cN
    fzfid
    fsumss
    @14
    @26
    @12
    cc
    wcel
    @16
    @12
    wceq
    @14
    cN
    @18
    nn0zd
    @14
    cA
    @11
    @23
    @14
    @7
    cN
    @29
    @18
    expcld
    mulcld
    @9
    @12
    vk
    cN
    @5
    @6
    cA
    @8
    @11
    cmul
    @22
    @4
    cN
    @7
    cexp
    oveq2
    oveq12d
    fsum1
    syl2anc
    eqtr3d
    mpteq2dva
    ply1term.1
    syl6reqr
end

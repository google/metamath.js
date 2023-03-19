include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cbits.mm"
include "cfv.mm"
include "csad.mm"
include "co.mm"
include "caddc.mm"
include "cv.mm"
include "cn0.mm"
include "wi.mm"
include "wss.mm"
include "bitsss.mm"
include "sadcl.mm"
include "mp2an.mm"
include "sseli.mm"
include "a1i.mm"
include "wb.mm"
include "cc0.mm"
include "c1.mm"
include "cfzo.mm"
include "cin.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "c2o.mm"
include "c0.mm"
include "wcad.mm"
include "c1o.mm"
include "cif.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cmin.mm"
include "cmpt.mm"
include "cseq.mm"
include "cres.mm"
include "ccnv.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "1nn0.mm"
include "nn0addcld.mm"
include "sadaddlem.mm"
include "zaddcld.mm"
include "bitsmod.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "elin.mm"
include "3bitr3g.mm"
include "cfz.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz2.mm"
include "syl.mm"
include "nn0zd.mm"
include "fzval3.mm"
include "eleqtrd.mm"
include "biantrud.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem sadadd
  let cA: class A
  let cB: class B
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cN: class N


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( ( bits ` A ) sadd ( bits ` B ) ) = ( bits ` ( A + B ) ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    vk
    cA
    cbits
    cfv
    #
    cB
    cbits
    cfv
    #
    csad
    co
    #
    cA
    cB
    caddc
    co
    #
    cbits
    cfv
    #
    @2
    vk
    cv
    #
    cn0
    wcel
    #
    @8
    @5
    wcel
    #
    @8
    @7
    wcel
    #
    @10
    @9
    wi
    @2
    @5
    cn0
    @8
    @3
    cn0
    wss
    @4
    cn0
    wss
    @5
    cn0
    wss
    cA
    bitsss
    cB
    bitsss
    @3
    @4
    sadcl
    mp2an
    sseli
    a1i
    @11
    @9
    wi
    @2
    @7
    cn0
    @8
    @6
    bitsss
    sseli
    a1i
    @2
    @9
    @10
    @11
    wb
    @2
    @9
    wa
    #
    @10
    @8
    cc0
    @8
    c1
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    @11
    @15
    wa
    #
    @10
    @11
    @12
    @8
    @5
    @14
    cin
    #
    wcel
    @8
    @7
    @14
    cin
    #
    wcel
    @16
    @17
    @12
    @18
    @19
    @8
    @12
    @18
    @6
    c2
    @13
    cexp
    co
    cmo
    co
    cbits
    cfv
    #
    @19
    @12
    cA
    cB
    vc
    vm
    c2o
    cn0
    vm
    cv
    #
    @3
    wcel
    @21
    @4
    wcel
    c0
    vc
    cv
    wcel
    wcad
    c1o
    c0
    cif
    cmpt2
    vn
    cn0
    vn
    cv
    #
    cc0
    wceq
    c0
    @22
    c1
    cmin
    co
    cif
    cmpt
    cc0
    cseq
    #
    vm
    vn
    cbits
    cn0
    cres
    ccnv
    #
    @13
    vc
    @23
    eqid
    @24
    eqid
    @0
    @1
    @9
    simpll
    #
    @0
    @1
    @9
    simplr
    #
    @12
    @8
    c1
    @2
    @9
    simpr
    #
    c1
    cn0
    wcel
    @12
    1nn0
    a1i
    nn0addcld
    #
    sadaddlem
    @12
    @6
    cz
    wcel
    @13
    cn0
    wcel
    @20
    @19
    wceq
    @12
    cA
    cB
    @25
    @26
    zaddcld
    @28
    @13
    @6
    bitsmod
    syl2anc
    eqtrd
    eleq2d
    @8
    @5
    @14
    elin
    @8
    @7
    @14
    elin
    3bitr3g
    @12
    @15
    @10
    @12
    @8
    cc0
    @8
    cfz
    co
    #
    @14
    @12
    @8
    cc0
    cuz
    cfv
    #
    wcel
    @8
    @29
    wcel
    @12
    @8
    cn0
    @30
    @27
    nn0uz
    syl6eleq
    cc0
    @8
    eluzfz2
    syl
    @12
    @8
    cz
    wcel
    @29
    @14
    wceq
    @12
    @8
    @27
    nn0zd
    cc0
    @8
    fzval3
    syl
    eleqtrd
    #
    biantrud
    @12
    @15
    @11
    @31
    biantrud
    3bitr4d
    ex
    pm5.21ndd
    eqrdv
end

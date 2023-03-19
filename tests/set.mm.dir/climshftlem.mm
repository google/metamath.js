include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cshi.mm"
include "cli.mm"
include "caddc.mm"
include "zaddcl.mm"
include "ancoms.mm"
include "wi.mm"
include "eluzsub.mm"
include "3com12.mm"
include "3expa.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "wb.mm"
include "zcn.mm"
include "eluzelcn.mm"
include "shftval.mm"
include "syl2an.mm"
include "adantlr.mm"
include "sylibrd.mm"
include "ralrimdva.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "syl6an.mm"
include "rexlimdva.mm"
include "ralimdv.mm"
include "anim2d.mm"
include "cvv.mm"
include "a1i.mm"
include "eqidd.mm"
include "clim.mm"
include "ovexd.mm"
include "3imtr4d.mm"

theorem climshftlem
  let cA: class A
  let cF: class F
  let cM: class M
  let vf: setvar f
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cV: class V
  assume climshft.1: |- F e. _V


  assert |- ( M e. ZZ -> ( F ~~> A -> ( F shift M ) ~~> A ) )

  proof
    cM
    cz
    wcel
    #
    cA
    cc
    wcel
    #
    vm
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @3
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vm
    vk
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vk
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @1
    vn
    cv
    #
    cF
    cM
    cshi
    co
    #
    cfv
    #
    cc
    wcel
    #
    @17
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    vn
    @2
    cuz
    cfv
    #
    wral
    #
    vm
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    cF
    cA
    cli
    wbr
    @16
    cA
    cli
    wbr
    @0
    @14
    @26
    @1
    @0
    @13
    @25
    vx
    crp
    @0
    @12
    @25
    vk
    cz
    @0
    @10
    cz
    wcel
    #
    wa
    #
    @10
    cM
    caddc
    co
    #
    cz
    wcel
    #
    @12
    @22
    vn
    @29
    cuz
    cfv
    #
    wral
    #
    @25
    @27
    @0
    @30
    @10
    cM
    zaddcl
    ancoms
    @28
    @12
    @22
    vn
    @31
    @28
    @15
    @31
    wcel
    #
    wa
    #
    @12
    @15
    cM
    cmin
    co
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @36
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    @22
    @34
    @35
    @11
    wcel
    #
    @12
    @41
    wi
    @0
    @27
    @33
    @42
    @27
    @0
    @33
    @42
    cM
    @10
    @15
    eluzsub
    3com12
    3expa
    @9
    @41
    vm
    @35
    @11
    @2
    @35
    wceq
    #
    @4
    @37
    @8
    @40
    @43
    @3
    @36
    cc
    @2
    @35
    cF
    fveq2
    #
    eleq1d
    @43
    @6
    @39
    @7
    clt
    @43
    @5
    @38
    cabs
    @43
    @3
    @36
    cA
    cmin
    @44
    oveq1d
    fveq2d
    breq1d
    anbi12d
    rspcv
    syl
    @0
    @33
    @22
    @41
    wb
    #
    @27
    @0
    cM
    cc
    wcel
    #
    @15
    cc
    wcel
    #
    @45
    @33
    cM
    zcn
    @29
    @15
    eluzelcn
    @46
    @47
    wa
    #
    @18
    @37
    @21
    @40
    @48
    @17
    @36
    cc
    cM
    @15
    cF
    climshft.1
    shftval
    #
    eleq1d
    @48
    @20
    @39
    @7
    clt
    @48
    @19
    @38
    cabs
    @48
    @17
    @36
    cA
    cmin
    @49
    oveq1d
    fveq2d
    breq1d
    anbi12d
    syl2an
    adantlr
    sylibrd
    ralrimdva
    @24
    @32
    vm
    @29
    cz
    @2
    @29
    wceq
    @22
    vn
    @23
    @31
    @2
    @29
    cuz
    fveq2
    raleqdv
    rspcev
    syl6an
    rexlimdva
    ralimdv
    anim2d
    @0
    vx
    cA
    @3
    vk
    vm
    cF
    cvv
    cF
    cvv
    wcel
    @0
    climshft.1
    a1i
    @0
    @2
    cz
    wcel
    wa
    @3
    eqidd
    clim
    @0
    vx
    cA
    @17
    vm
    vn
    @16
    cvv
    @0
    cF
    cM
    cshi
    ovexd
    @0
    @15
    cz
    wcel
    wa
    @17
    eqidd
    clim
    3imtr4d
end

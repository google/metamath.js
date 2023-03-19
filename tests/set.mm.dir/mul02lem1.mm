include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cmul.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "cc.mm"
include "cv.mm"
include "c1.mm"
include "wceq.mm"
include "caddc.mm"
include "wrex.mm"
include "0re.mm"
include "remulcl.mm"
include "mpan.mm"
include "ax-rrecex.mm"
include "sylan.mm"
include "adantr.mm"
include "00id.mm"
include "oveq2i.mm"
include "eqcomi.mm"
include "simprl.mm"
include "recnd.mm"
include "simplll.mm"
include "mulcld.mm"
include "simplr.mm"
include "0cn.mm"
include "mul32.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mul31.mm"
include "simprr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "mulid2.mm"
include "ad2antlr.mm"
include "adddi.mm"
include "mp3an23.mm"
include "syl.mm"
include "oveq12d.mm"
include "3eqtr3a.mm"
include "rexlimddv.mm"

theorem mul02lem1
  let cA: class A
  let cB: class B
  let vy: setvar y


  assert |- ( ( ( A e. RR /\ ( 0 x. A ) =/= 0 ) /\ B e. CC ) -> B = ( B + B ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cmul
    co
    #
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    wa
    #
    @1
    vy
    cv
    #
    cmul
    co
    #
    c1
    wceq
    #
    cB
    cB
    cB
    caddc
    co
    #
    wceq
    vy
    cr
    @3
    @8
    vy
    cr
    wrex
    #
    @4
    @0
    @1
    cr
    wcel
    #
    @2
    @10
    cc0
    cr
    wcel
    @0
    @11
    0re
    cc0
    cA
    remulcl
    mpan
    vy
    @1
    ax-rrecex
    sylan
    adantr
    @5
    @6
    cr
    wcel
    #
    @8
    wa
    #
    wa
    #
    @6
    cA
    cmul
    co
    #
    cB
    cmul
    co
    #
    cc0
    cmul
    co
    #
    @16
    cc0
    cc0
    caddc
    co
    #
    cmul
    co
    #
    cB
    @9
    @19
    @17
    @18
    cc0
    @16
    cmul
    00id
    oveq2i
    eqcomi
    @14
    @17
    @15
    cc0
    cmul
    co
    #
    cB
    cmul
    co
    #
    cB
    @14
    @15
    cc
    wcel
    #
    @4
    @17
    @21
    wceq
    #
    @14
    @6
    cA
    @14
    @6
    @5
    @12
    @8
    simprl
    recnd
    #
    @14
    cA
    @0
    @2
    @4
    @13
    simplll
    recnd
    #
    mulcld
    #
    @3
    @4
    @13
    simplr
    #
    @22
    @4
    cc0
    cc
    wcel
    #
    @23
    0cn
    @15
    cB
    cc0
    mul32
    mp3an3
    syl2anc
    @14
    @21
    c1
    cB
    cmul
    co
    #
    cB
    @14
    @20
    c1
    cB
    cmul
    @14
    @20
    @7
    c1
    @14
    @6
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @20
    @7
    wceq
    #
    @24
    @25
    @30
    @31
    @28
    @32
    0cn
    @6
    cA
    cc0
    mul31
    mp3an3
    syl2anc
    @5
    @12
    @8
    simprr
    eqtrd
    oveq1d
    @4
    @29
    cB
    wceq
    @3
    @13
    cB
    mulid2
    ad2antlr
    eqtrd
    eqtrd
    #
    @14
    @19
    @17
    @17
    caddc
    co
    #
    @9
    @14
    @16
    cc
    wcel
    #
    @19
    @34
    wceq
    #
    @14
    @15
    cB
    @26
    @27
    mulcld
    @35
    @28
    @28
    @36
    0cn
    0cn
    @16
    cc0
    cc0
    adddi
    mp3an23
    syl
    @14
    @17
    cB
    @17
    cB
    caddc
    @33
    @33
    oveq12d
    eqtrd
    3eqtr3a
    rexlimddv
end

include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "csegle.mm"
include "wbr.mm"
include "cv.mm"
include "cbtwn.mm"
include "ccgr.mm"
include "wrex.mm"
include "brsegle.mm"
include "wb.mm"
include "brsegle2.mm"
include "3com23.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "syl6bbr.mm"
include "weq.mm"
include "simpl1.mm"
include "simpl3l.mm"
include "simprr.mm"
include "simprl.mm"
include "simpl3r.mm"
include "simprll.mm"
include "simprrl.mm"
include "btwnexchand.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simprrr.mm"
include "simprlr.mm"
include "cgrtrand.mm"
include "endofsegidand.mm"
include "opeq2.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi2d.mm"
include "wceq.mm"
include "btwncomand.mm"
include "wi.mm"
include "btwnswapid.mm"
include "syl13anc.mm"
include "adantr.mm"
include "mp2and.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "exp31.mm"
include "rexlimdvv.mm"
include "sylbid.mm"

theorem segleantisym
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vy: setvar y
  let vt: setvar t


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> ( ( <. A , B >. Seg<_ <. C , D >. /\ <. C , D >. Seg<_ <. A , B >. ) -> <. A , B >. Cgr <. C , D >. ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    csegle
    wbr
    #
    @10
    @9
    csegle
    wbr
    #
    wa
    #
    vy
    cv
    #
    @10
    cbtwn
    wbr
    #
    @9
    cC
    @14
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cD
    cC
    vt
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @20
    @9
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    vt
    @1
    wrex
    vy
    @1
    wrex
    #
    @9
    @10
    ccgr
    wbr
    #
    @8
    @13
    @18
    vy
    @1
    wrex
    #
    @23
    vt
    @1
    wrex
    #
    wa
    @25
    @8
    @11
    @27
    @12
    @28
    vy
    cA
    cB
    cC
    cD
    cN
    brsegle
    @0
    @7
    @4
    @12
    @28
    wb
    vt
    cC
    cD
    cA
    cB
    cN
    brsegle2
    3com23
    anbi12d
    @18
    @23
    vy
    vt
    @1
    @1
    reeanv
    syl6bbr
    @8
    @24
    @26
    vy
    vt
    @1
    @1
    @8
    @14
    @1
    wcel
    #
    @19
    @1
    wcel
    #
    wa
    #
    @24
    @26
    vt
    vy
    weq
    #
    @8
    @31
    wa
    #
    @24
    wa
    #
    @26
    @33
    @24
    cC
    @19
    @14
    cN
    @0
    @4
    @7
    @31
    simpl1
    #
    @5
    @6
    @0
    @4
    @31
    simpl3l
    #
    @8
    @29
    @30
    simprr
    #
    @8
    @29
    @30
    simprl
    #
    @33
    @24
    cC
    @14
    cD
    @19
    cN
    @35
    @36
    @38
    @5
    @6
    @0
    @4
    @31
    simpl3r
    #
    @37
    @33
    @15
    @17
    @23
    simprll
    @33
    @18
    @21
    @22
    simprrl
    btwnexchand
    @33
    @24
    cC
    @19
    cA
    cB
    cC
    @14
    cN
    @35
    @36
    @37
    @2
    @3
    @0
    @7
    @31
    simpl2l
    @2
    @3
    @0
    @7
    @31
    simpl2r
    @36
    @38
    @33
    @18
    @21
    @22
    simprrr
    @33
    @15
    @17
    @23
    simprlr
    cgrtrand
    endofsegidand
    @32
    @34
    @33
    @18
    cD
    @16
    cbtwn
    wbr
    #
    @16
    @9
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    wa
    #
    @26
    @32
    @24
    @43
    @33
    @32
    @23
    @42
    @18
    @32
    @21
    @40
    @22
    @41
    @32
    @20
    @16
    cD
    cbtwn
    @19
    @14
    cC
    opeq2
    #
    breq2d
    @32
    @20
    @16
    @9
    ccgr
    @45
    breq1d
    anbi12d
    anbi2d
    anbi2d
    @44
    cD
    @14
    wceq
    #
    @26
    @44
    cD
    @14
    cC
    cop
    cbtwn
    wbr
    #
    @14
    cD
    cC
    cop
    cbtwn
    wbr
    #
    @46
    @33
    @43
    cD
    cC
    @14
    cN
    @35
    @39
    @36
    @38
    @33
    @18
    @40
    @41
    simprrl
    btwncomand
    @33
    @43
    @14
    cC
    cD
    cN
    @35
    @38
    @36
    @39
    @33
    @15
    @17
    @42
    simprll
    btwncomand
    @33
    @47
    @48
    wa
    @46
    wi
    #
    @43
    @33
    @0
    @6
    @29
    @5
    @49
    @35
    @39
    @38
    @36
    cD
    @14
    cC
    cN
    btwnswapid
    syl13anc
    adantr
    mp2and
    @44
    @26
    @46
    @17
    @33
    @15
    @17
    @42
    simprlr
    @46
    @10
    @16
    @9
    ccgr
    cD
    @14
    cC
    opeq2
    breq2d
    syl5ibrcom
    mpd
    syl6bi
    mpcom
    exp31
    rexlimdvv
    sylbid
end

include "clines2.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cline2.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cee.mm"
include "cfv.mm"
include "wrex.mm"
include "cn.mm"
include "wi.mm"
include "ellines.mm"
include "w3a.mm"
include "wss.mm"
include "simpll1.mm"
include "simpll2.mm"
include "simpll3.mm"
include "simplr.mm"
include "liness.mm"
include "syl13anc.mm"
include "simprll.mm"
include "sseldd.mm"
include "simprlr.mm"
include "simplll.mm"
include "adantl.mm"
include "simprrl.mm"
include "necomd.mm"
include "lineelsb2.mm"
include "syl132anc.mm"
include "mpd.mm"
include "linecom.mm"
include "eqtrd.mm"
include "neeq2.mm"
include "anbi2d.mm"
include "anbi1d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "simp1.mm"
include "simp2l.mm"
include "syl2anc.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp1l3.mm"
include "simp1r.mm"
include "simp2rr.mm"
include "simp3.mm"
include "simplld.mm"
include "eleqtrd.mm"
include "simp2rl.mm"
include "simp2lr.mm"
include "3eqtrd.mm"
include "3expa.mm"
include "expcom.mm"
include "pm2.61ine.mm"
include "expr.mm"
include "mp2and.mm"
include "ex.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "3impib.mm"

theorem linethru
  let cA: class A
  let cP: class P
  let cQ: class Q
  let va: setvar a
  let vb: setvar b
  let vn: setvar n


  assert |- ( ( A e. LinesEE /\ ( P e. A /\ Q e. A ) /\ P =/= Q ) -> A = ( P Line Q ) )

  proof
    cA
    clines2
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    #
    cA
    cP
    cQ
    cline2
    co
    #
    wceq
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    cA
    @7
    @8
    cline2
    co
    #
    wceq
    #
    wa
    #
    vb
    vn
    cv
    #
    cee
    cfv
    #
    wrex
    #
    va
    @14
    wrex
    vn
    cn
    wrex
    @3
    @4
    wa
    #
    @6
    wi
    #
    cA
    vn
    vb
    va
    ellines
    @15
    @17
    vn
    va
    cn
    @14
    @13
    cn
    wcel
    #
    @7
    @14
    wcel
    #
    wa
    @12
    @17
    vb
    @14
    @18
    @19
    @8
    @14
    wcel
    #
    @12
    @17
    wi
    @18
    @19
    @20
    w3a
    #
    @9
    @11
    @17
    @21
    @9
    wa
    #
    @17
    @11
    cP
    @10
    wcel
    #
    cQ
    @10
    wcel
    #
    wa
    #
    @4
    wa
    #
    @10
    @5
    wceq
    #
    wi
    @22
    @26
    @27
    @22
    @26
    wa
    #
    cP
    @14
    wcel
    #
    cQ
    @14
    wcel
    #
    @27
    @28
    @10
    @14
    cP
    @28
    @18
    @19
    @20
    @9
    @10
    @14
    wss
    @18
    @19
    @20
    @9
    @26
    simpll1
    @18
    @19
    @20
    @9
    @26
    simpll2
    @18
    @19
    @20
    @9
    @26
    simpll3
    @21
    @9
    @26
    simplr
    @7
    @8
    @13
    liness
    syl13anc
    #
    @22
    @23
    @24
    @4
    simprll
    sseldd
    @28
    @10
    @14
    cQ
    @31
    @22
    @23
    @24
    @4
    simprlr
    #
    sseldd
    @22
    @26
    @29
    @30
    wa
    #
    @27
    @22
    @26
    @33
    wa
    #
    wa
    #
    @27
    wi
    #
    cQ
    @7
    cQ
    @7
    wceq
    #
    @36
    @22
    @25
    cP
    @7
    wne
    #
    wa
    #
    @33
    wa
    #
    wa
    #
    @10
    cP
    @7
    cline2
    co
    #
    wceq
    #
    wi
    @41
    @10
    @7
    cP
    cline2
    co
    #
    @42
    @41
    @23
    @10
    @44
    wceq
    #
    @40
    @23
    @22
    @23
    @24
    @38
    @33
    simplll
    adantl
    @41
    @18
    @19
    @20
    @9
    @29
    @7
    cP
    wne
    #
    @23
    @45
    wi
    @18
    @19
    @20
    @9
    @40
    simpll1
    #
    @18
    @19
    @20
    @9
    @40
    simpll2
    #
    @18
    @19
    @20
    @9
    @40
    simpll3
    @21
    @9
    @40
    simplr
    @22
    @39
    @29
    @30
    simprrl
    #
    @41
    cP
    @7
    @22
    @25
    @38
    @33
    simprlr
    necomd
    #
    @7
    @8
    cP
    @13
    lineelsb2
    syl132anc
    mpd
    @41
    @18
    @19
    @29
    @46
    @44
    @42
    wceq
    @47
    @48
    @49
    @50
    @7
    cP
    @13
    linecom
    syl13anc
    eqtrd
    @37
    @35
    @41
    @27
    @43
    @37
    @34
    @40
    @22
    @37
    @26
    @39
    @33
    @37
    @4
    @38
    @25
    cQ
    @7
    cP
    neeq2
    anbi2d
    anbi1d
    anbi2d
    @37
    @5
    @42
    @10
    cQ
    @7
    cP
    cline2
    oveq2
    eqeq2d
    imbi12d
    mpbiri
    @35
    cQ
    @7
    wne
    #
    @27
    @22
    @34
    @51
    @27
    @22
    @34
    @51
    w3a
    #
    @10
    cQ
    @7
    cline2
    co
    #
    cQ
    cP
    cline2
    co
    #
    @5
    @52
    @10
    @7
    cQ
    cline2
    co
    #
    @53
    @52
    @24
    @10
    @55
    wceq
    #
    @52
    @22
    @26
    @24
    @22
    @34
    @51
    simp1
    @22
    @26
    @33
    @51
    simp2l
    #
    @32
    syl2anc
    @52
    @18
    @19
    @20
    @9
    @30
    @7
    cQ
    wne
    #
    @24
    @56
    wi
    @18
    @19
    @20
    @9
    @34
    @51
    simp1l1
    #
    @18
    @19
    @20
    @9
    @34
    @51
    simp1l2
    #
    @18
    @19
    @20
    @9
    @34
    @51
    simp1l3
    @21
    @9
    @34
    @51
    simp1r
    @29
    @30
    @26
    @22
    @51
    simp2rr
    #
    @52
    cQ
    @7
    @22
    @34
    @51
    simp3
    #
    necomd
    #
    @7
    @8
    cQ
    @13
    lineelsb2
    syl132anc
    mpd
    @52
    @18
    @19
    @30
    @58
    @55
    @53
    wceq
    @59
    @60
    @61
    @63
    @7
    cQ
    @13
    linecom
    syl13anc
    eqtrd
    #
    @52
    cP
    @53
    wcel
    #
    @53
    @54
    wceq
    #
    @52
    cP
    @10
    @53
    @52
    @23
    @24
    @4
    @57
    simplld
    @64
    eleqtrd
    @52
    @18
    @30
    @19
    @51
    @29
    cQ
    cP
    wne
    #
    @65
    @66
    wi
    @59
    @61
    @60
    @62
    @29
    @30
    @26
    @22
    @51
    simp2rl
    #
    @52
    cP
    cQ
    @25
    @4
    @33
    @22
    @51
    simp2lr
    necomd
    #
    cQ
    @7
    cP
    @13
    lineelsb2
    syl132anc
    mpd
    @52
    @18
    @30
    @29
    @67
    @54
    @5
    wceq
    @59
    @61
    @68
    @69
    cQ
    cP
    @13
    linecom
    syl13anc
    3eqtrd
    3expa
    expcom
    pm2.61ine
    expr
    mp2and
    ex
    @11
    @16
    @26
    @6
    @27
    @11
    @3
    @25
    @4
    @11
    @1
    @23
    @2
    @24
    cA
    @10
    cP
    eleq2
    cA
    @10
    cQ
    eleq2
    anbi12d
    anbi1d
    cA
    @10
    @5
    eqeq1
    imbi12d
    syl5ibrcom
    expimpd
    3expa
    rexlimdva
    rexlimivv
    sylbi
    3impib
end

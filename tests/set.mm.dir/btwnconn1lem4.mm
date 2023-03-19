include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "wa.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "ccgr3.mm"
include "simp1rl.mm"
include "simp2rl.mm"
include "jca.mm"
include "adantl.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp3l.mm"
include "btwnexch3.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mpd.mm"
include "simp3lr.mm"
include "wb.mm"
include "simp23.mm"
include "simp3r.mm"
include "cgrcomlr.mm"
include "cgrcom.mm"
include "bitrd.mm"
include "mpbid.mm"
include "3simpa.mm"
include "anim1i.mm"
include "btwnconn1lem3.mm"
include "syl3anr1.mm"
include "simp22.mm"
include "simp2rr.mm"
include "simp2lr.mm"
include "cgrcomland.mm"
include "cgrtr3and.mm"
include "brcgr3.mm"
include "syl133anc.mm"
include "mpbir3and.mm"
include "simpl.mm"
include "simpr.mm"
include "3jca.mm"
include "3anim3i.mm"
include "3anim1i.mm"
include "btwnconn1lem1.mm"
include "syl2an.mm"
include "cgrrflx2d.mm"
include "simp1l2.mm"
include "cofs.mm"
include "brofs2.mm"
include "anbi1d.mm"
include "5segofs.mm"
include "sylbird.mm"
include "syl333anc.mm"
include "mp2and.mm"

theorem btwnconn1lem4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ c e. ( EE ` N ) ) /\ ( d e. ( EE ` N ) /\ b e. ( EE ` N ) ) ) /\ ( ( ( A =/= B /\ B =/= C /\ C =/= c ) /\ ( B Btwn <. A , C >. /\ B Btwn <. A , D >. ) ) /\ ( ( D Btwn <. A , c >. /\ <. D , c >. Cgr <. C , D >. ) /\ ( C Btwn <. A , d >. /\ <. C , d >. Cgr <. C , D >. ) ) /\ ( ( c Btwn <. A , b >. /\ <. c , b >. Cgr <. C , B >. ) /\ ( d Btwn <. A , b >. /\ <. d , b >. Cgr <. D , B >. ) ) ) ) -> <. d , c >. Cgr <. D , C >. )

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
    w3a
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    vc
    cv
    #
    @1
    wcel
    #
    w3a
    #
    vd
    cv
    #
    @1
    wcel
    #
    vb
    cv
    #
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    cC
    @7
    wne
    #
    w3a
    #
    cB
    cA
    cC
    cop
    cbtwn
    wbr
    #
    cB
    cA
    cD
    cop
    cbtwn
    wbr
    #
    wa
    #
    wa
    #
    cD
    cA
    @7
    cop
    cbtwn
    wbr
    #
    cD
    @7
    cop
    cC
    cD
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    cC
    cA
    @10
    cop
    cbtwn
    wbr
    #
    cC
    @10
    cop
    #
    @25
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    @7
    cA
    @12
    cop
    #
    cbtwn
    wbr
    #
    @7
    @12
    cop
    cC
    cB
    cop
    ccgr
    wbr
    #
    wa
    @10
    @33
    cbtwn
    wbr
    @10
    @12
    cop
    cD
    cB
    cop
    ccgr
    wbr
    wa
    #
    wa
    #
    w3a
    #
    wa
    #
    cC
    cB
    @10
    cop
    #
    cbtwn
    wbr
    #
    cB
    @29
    cop
    @12
    @7
    cD
    cop
    #
    cop
    ccgr3
    wbr
    #
    cB
    @7
    cop
    @12
    cC
    cop
    ccgr
    wbr
    #
    cC
    @7
    cop
    @7
    cC
    cop
    ccgr
    wbr
    #
    wa
    #
    w3a
    #
    @17
    @10
    @7
    cop
    #
    cD
    cC
    cop
    #
    ccgr
    wbr
    #
    @39
    @41
    @43
    @46
    @39
    @20
    @28
    wa
    #
    @41
    @38
    @51
    @15
    @38
    @20
    @28
    @20
    @21
    @19
    @32
    @37
    simp1rl
    @28
    @30
    @27
    @23
    @37
    simp2rl
    jca
    adantl
    @15
    @51
    @41
    wi
    #
    @38
    @15
    @0
    @2
    @3
    @5
    @11
    @52
    @0
    @2
    @3
    @9
    @14
    simp11
    #
    @0
    @2
    @3
    @9
    @14
    simp12
    @0
    @2
    @3
    @9
    @14
    simp13
    #
    @4
    @5
    @6
    @8
    @14
    simp21
    #
    @4
    @9
    @11
    @13
    simp3l
    #
    cA
    cB
    cC
    @10
    cN
    btwnexch3
    syl122anc
    adantr
    mpd
    @39
    @43
    cB
    cC
    cop
    #
    @12
    @7
    cop
    #
    ccgr
    wbr
    #
    @40
    @12
    cD
    cop
    ccgr
    wbr
    #
    @29
    @42
    ccgr
    wbr
    #
    @39
    @35
    @59
    @38
    @35
    @15
    @34
    @35
    @36
    @23
    @32
    simp3lr
    adantl
    @15
    @35
    @59
    wb
    @38
    @15
    @35
    @58
    @57
    ccgr
    wbr
    #
    @59
    @15
    @0
    @8
    @13
    @5
    @3
    @35
    @62
    wb
    @53
    @4
    @5
    @6
    @8
    @14
    simp23
    #
    @4
    @9
    @11
    @13
    simp3r
    #
    @55
    @54
    @7
    @12
    cC
    cB
    cN
    cgrcomlr
    syl122anc
    @15
    @0
    @13
    @8
    @3
    @5
    @62
    @59
    wb
    @53
    @64
    @63
    @54
    @55
    @12
    @7
    cB
    cC
    cN
    cgrcom
    syl122anc
    bitrd
    adantr
    mpbid
    @23
    @16
    @17
    wa
    #
    @22
    wa
    #
    @15
    @32
    @37
    @60
    @19
    @65
    @22
    @16
    @17
    @18
    3simpa
    anim1i
    #
    cA
    cB
    cC
    cD
    cN
    vb
    vc
    vd
    btwnconn1lem3
    syl3anr1
    @15
    @38
    cC
    @10
    @7
    cD
    cC
    cD
    cN
    @53
    @55
    @56
    @63
    @4
    @5
    @6
    @8
    @14
    simp22
    #
    @55
    @68
    @38
    @30
    @15
    @28
    @30
    @27
    @23
    @37
    simp2rr
    adantl
    @15
    @38
    cD
    @7
    cC
    cD
    cN
    @53
    @68
    @63
    @55
    @68
    @38
    @26
    @15
    @24
    @26
    @31
    @23
    @37
    simp2lr
    adantl
    cgrcomland
    cgrtr3and
    @15
    @43
    @59
    @60
    @61
    w3a
    wb
    #
    @38
    @15
    @0
    @3
    @5
    @11
    @13
    @8
    @6
    @69
    @53
    @54
    @55
    @56
    @64
    @63
    @68
    cB
    cC
    @10
    @12
    @7
    cD
    cN
    brcgr3
    syl133anc
    adantr
    mpbir3and
    @39
    @44
    @45
    @15
    @4
    @9
    @11
    @13
    @13
    w3a
    #
    w3a
    @66
    @32
    @37
    w3a
    @44
    @38
    @14
    @70
    @4
    @9
    @14
    @11
    @13
    @13
    @11
    @13
    simpl
    @11
    @13
    simpr
    #
    @71
    3jca
    3anim3i
    @23
    @66
    @32
    @37
    @67
    3anim1i
    cA
    cB
    cC
    cD
    cN
    @12
    vb
    vc
    vd
    btwnconn1lem1
    syl2an
    @15
    @45
    @38
    @15
    cC
    @7
    cN
    @53
    @55
    @63
    cgrrflx2d
    adantr
    jca
    3jca
    @38
    @17
    @15
    @16
    @17
    @18
    @22
    @32
    @37
    simp1l2
    adantl
    @15
    @47
    @17
    wa
    #
    @50
    wi
    #
    @38
    @15
    @0
    @3
    @5
    @11
    @8
    @13
    @8
    @6
    @5
    @73
    @53
    @54
    @55
    @56
    @63
    @64
    @63
    @68
    @55
    @0
    @3
    @5
    w3a
    @11
    @8
    @13
    w3a
    @8
    @6
    @5
    w3a
    w3a
    #
    @72
    @57
    @48
    cop
    @58
    @49
    cop
    cofs
    wbr
    #
    @17
    wa
    @50
    @74
    @75
    @47
    @17
    cB
    cC
    @10
    @7
    @12
    @7
    cD
    cC
    cN
    brofs2
    anbi1d
    cB
    cC
    @10
    @7
    @12
    @7
    cD
    cC
    cN
    5segofs
    sylbird
    syl333anc
    adantr
    mp2and
end

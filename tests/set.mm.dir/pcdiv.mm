include "cprime.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cn.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "cpc.mm"
include "cv.mm"
include "wceq.mm"
include "cexp.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmin.mm"
include "wrex.mm"
include "cio.mm"
include "cq.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp3.mm"
include "znq.mm"
include "syl2anc.mm"
include "zcnd.mm"
include "nncnd.mm"
include "simp2r.mm"
include "nnne0d.mm"
include "divne0d.mm"
include "eqid.mm"
include "pcval.mm"
include "syl12anc.mm"
include "pczpre.mm"
include "3adant3.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "sylan2.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "jctil.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "breq2.mm"
include "rabbidv.mm"
include "supeq1d.mm"
include "oveq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "cvv.mm"
include "weu.mm"
include "wb.mm"
include "ovex.mm"
include "pceu.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "2rexbidv.mm"
include "iota2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem pcdiv
  let cA: class A
  let cB: class B
  let cP: class P
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( P e. Prime /\ ( A e. ZZ /\ A =/= 0 ) /\ B e. NN ) -> ( P pCnt ( A / B ) ) = ( ( P pCnt A ) - ( P pCnt B ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cn
    wcel
    #
    w3a
    #
    cP
    cA
    cB
    cdiv
    co
    #
    cpc
    co
    #
    @6
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vz
    cv
    #
    cP
    vn
    cv
    cexp
    co
    #
    @8
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @13
    @9
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cmin
    co
    #
    wceq
    #
    wa
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    vz
    cio
    #
    cP
    cA
    cpc
    co
    #
    cP
    cB
    cpc
    co
    #
    cmin
    co
    #
    @5
    @0
    @6
    cq
    wcel
    #
    @6
    cc0
    wne
    #
    @7
    @24
    wceq
    @0
    @3
    @4
    simp1
    #
    @5
    @1
    @4
    @28
    @0
    @1
    @2
    @4
    simp2l
    #
    @0
    @3
    @4
    simp3
    #
    cA
    cB
    znq
    syl2anc
    #
    @5
    cA
    cB
    @5
    cA
    @31
    zcnd
    @5
    cB
    @32
    nncnd
    @0
    @1
    @2
    @4
    simp2r
    @5
    cB
    @32
    nnne0d
    divne0d
    #
    vx
    vy
    vz
    cP
    @16
    @19
    vn
    @6
    @16
    eqid
    #
    @19
    eqid
    #
    pcval
    syl12anc
    @5
    @11
    @27
    @20
    wceq
    #
    wa
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    @24
    @27
    wceq
    #
    @5
    @1
    @4
    @6
    @6
    wceq
    #
    @27
    @13
    cA
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    @13
    cB
    cdvds
    wbr
    #
    vn
    cn0
    crab
    #
    cr
    clt
    csup
    #
    cmin
    co
    #
    wceq
    #
    wa
    #
    @39
    @31
    @32
    @5
    @49
    @41
    @5
    @25
    @44
    @26
    @47
    cmin
    @0
    @3
    @25
    @44
    wceq
    @4
    cP
    @44
    vn
    cA
    @44
    eqid
    pczpre
    3adant3
    @0
    @4
    @26
    @47
    wceq
    #
    @3
    @4
    @0
    cB
    cz
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    @51
    @4
    @52
    @53
    cB
    nnz
    cB
    nnne0
    jca
    cP
    @47
    vn
    cB
    @47
    eqid
    pczpre
    sylan2
    3adant2
    oveq12d
    @6
    eqid
    jctil
    @38
    @50
    @6
    cA
    @9
    cdiv
    co
    #
    wceq
    #
    @27
    @44
    @19
    cmin
    co
    #
    wceq
    #
    wa
    vx
    vy
    cA
    cB
    cz
    cn
    @8
    cA
    wceq
    #
    @11
    @55
    @37
    @57
    @58
    @10
    @54
    @6
    @8
    cA
    @9
    cdiv
    oveq1
    eqeq2d
    @58
    @20
    @56
    @27
    @58
    @16
    @44
    @19
    cmin
    @58
    cr
    @15
    @43
    clt
    @58
    @14
    @42
    vn
    cn0
    @8
    cA
    @13
    cdvds
    breq2
    rabbidv
    supeq1d
    oveq1d
    eqeq2d
    anbi12d
    @9
    cB
    wceq
    #
    @55
    @41
    @57
    @49
    @59
    @54
    @6
    @6
    @9
    cB
    cA
    cdiv
    oveq2
    eqeq2d
    @59
    @56
    @48
    @27
    @59
    @19
    @47
    @44
    cmin
    @59
    cr
    @18
    @46
    clt
    @59
    @17
    @45
    vn
    cn0
    @9
    cB
    @13
    cdvds
    breq2
    rabbidv
    supeq1d
    oveq2d
    eqeq2d
    anbi12d
    rspc2ev
    syl3anc
    @5
    @27
    cvv
    wcel
    @23
    vz
    weu
    #
    @39
    @40
    wb
    @25
    @26
    cmin
    ovex
    @5
    @0
    @28
    @29
    @60
    @30
    @33
    @34
    vx
    vy
    vz
    cP
    @16
    @19
    vn
    @6
    @35
    @36
    pceu
    syl12anc
    @23
    @39
    vz
    @27
    cvv
    @12
    @27
    wceq
    #
    @22
    @38
    vx
    vy
    cz
    cn
    @61
    @21
    @37
    @11
    @12
    @27
    @20
    eqeq1
    anbi2d
    2rexbidv
    iota2
    sylancr
    mpbid
    eqtrd
end

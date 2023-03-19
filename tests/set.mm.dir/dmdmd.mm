include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "sseq1.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "choccl.mm"
include "imim1i.mm"
include "com12.mm"
include "adantl.mm"
include "chsscon3.mm"
include "biimpd.mm"
include "adantll.mm"
include "fveq2.mm"
include "wb.mm"
include "chjcl.mm"
include "syl2an.mm"
include "chdmm3.mm"
include "sylan.mm"
include "chdmj4.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "anasss.mm"
include "chincl.mm"
include "chdmj2.mm"
include "sylan2.mm"
include "chdmm4.mm"
include "ineq2d.mm"
include "ancoms.mm"
include "syl5ib.mm"
include "imim12d.mm"
include "syld.mm"
include "ex.mm"
include "com23.mm"
include "syl5.mm"
include "ralrimdv.mm"
include "sseq2.mm"
include "ineq1.mm"
include "chsscon2.mm"
include "biimprd.mm"
include "chdmj1.mm"
include "chdmm2.mm"
include "oveq2d.mm"
include "impbid.mm"
include "mdbr.mm"
include "dmdbr.mm"
include "3bitr4rd.mm"

theorem dmdmd
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH* B <-> ( _|_ ` A ) MH ( _|_ ` B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    vy
    cv
    #
    cB
    cort
    cfv
    #
    wss
    #
    @3
    cA
    cort
    cfv
    #
    chj
    co
    #
    @4
    cin
    #
    @3
    @6
    @4
    cin
    #
    chj
    co
    #
    wceq
    #
    wi
    #
    vy
    cch
    wral
    #
    cB
    vx
    cv
    #
    wss
    #
    @14
    cA
    cin
    #
    cB
    chj
    co
    #
    @14
    cA
    cB
    chj
    co
    #
    cin
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    #
    @6
    @4
    cmd
    wbr
    #
    cA
    cB
    cdmd
    wbr
    @2
    @13
    @22
    @2
    @13
    @21
    vx
    cch
    @13
    @14
    cort
    cfv
    #
    cch
    wcel
    #
    @24
    @4
    wss
    #
    @24
    @6
    chj
    co
    #
    @4
    cin
    #
    @24
    @9
    chj
    co
    #
    wceq
    #
    wi
    #
    wi
    #
    @2
    @14
    cch
    wcel
    #
    @21
    wi
    @12
    @31
    vy
    @24
    cch
    @3
    @24
    wceq
    #
    @5
    @26
    @11
    @30
    @3
    @24
    @4
    sseq1
    @34
    @8
    @28
    @10
    @29
    @34
    @7
    @27
    @4
    @3
    @24
    @6
    chj
    oveq1
    ineq1d
    @3
    @24
    @9
    chj
    oveq1
    eqeq12d
    imbi12d
    rspccv
    @2
    @33
    @32
    @21
    @2
    @33
    @32
    @21
    wi
    @2
    @33
    wa
    #
    @32
    @31
    @21
    @33
    @32
    @31
    wi
    @2
    @32
    @33
    @31
    @33
    @25
    @31
    @14
    choccl
    #
    imim1i
    com12
    adantl
    @35
    @15
    @26
    @30
    @20
    @1
    @33
    @15
    @26
    wi
    @0
    @1
    @33
    wa
    @15
    @26
    cB
    @14
    chsscon3
    biimpd
    adantll
    @30
    @28
    cort
    cfv
    #
    @29
    cort
    cfv
    #
    wceq
    #
    @35
    @20
    @28
    @29
    cort
    fveq2
    @33
    @2
    @39
    @20
    wb
    @33
    @2
    wa
    #
    @37
    @17
    @38
    @19
    @33
    @0
    @1
    @37
    @17
    wceq
    @33
    @0
    wa
    #
    @1
    wa
    #
    @37
    @27
    cort
    cfv
    #
    cB
    chj
    co
    #
    @17
    @41
    @27
    cch
    wcel
    #
    @1
    @37
    @44
    wceq
    @33
    @25
    @6
    cch
    wcel
    #
    @45
    @0
    @36
    cA
    choccl
    #
    @24
    @6
    chjcl
    syl2an
    @27
    cB
    chdmm3
    sylan
    @42
    @43
    @16
    cB
    chj
    @41
    @43
    @16
    wceq
    @1
    @14
    cA
    chdmj4
    adantr
    oveq1d
    eqtrd
    anasss
    @40
    @38
    @14
    @9
    cort
    cfv
    #
    cin
    #
    @19
    @2
    @33
    @9
    cch
    wcel
    #
    @38
    @49
    wceq
    @0
    @46
    @4
    cch
    wcel
    #
    @50
    @1
    @47
    cB
    choccl
    #
    @6
    @4
    chincl
    syl2an
    @14
    @9
    chdmj2
    sylan2
    @40
    @48
    @18
    @14
    @2
    @48
    @18
    wceq
    @33
    cA
    cB
    chdmm4
    adantl
    ineq2d
    eqtrd
    eqeq12d
    ancoms
    syl5ib
    imim12d
    syld
    ex
    com23
    syl5
    ralrimdv
    @2
    @22
    @12
    vy
    cch
    @22
    @3
    cort
    cfv
    #
    cch
    wcel
    #
    cB
    @53
    wss
    #
    @53
    cA
    cin
    #
    cB
    chj
    co
    #
    @53
    @18
    cin
    #
    wceq
    #
    wi
    #
    wi
    #
    @2
    @3
    cch
    wcel
    #
    @12
    wi
    @21
    @60
    vx
    @53
    cch
    @14
    @53
    wceq
    #
    @15
    @55
    @20
    @59
    @14
    @53
    cB
    sseq2
    @63
    @17
    @57
    @19
    @58
    @63
    @16
    @56
    cB
    chj
    @14
    @53
    cA
    ineq1
    oveq1d
    @14
    @53
    @18
    ineq1
    eqeq12d
    imbi12d
    rspccv
    @2
    @62
    @61
    @12
    @2
    @62
    @61
    @12
    wi
    @2
    @62
    wa
    #
    @61
    @60
    @12
    @62
    @61
    @60
    wi
    @2
    @61
    @62
    @60
    @62
    @54
    @60
    @3
    choccl
    #
    imim1i
    com12
    adantl
    @64
    @5
    @55
    @59
    @11
    @1
    @62
    @5
    @55
    wi
    @0
    @1
    @62
    wa
    @55
    @5
    cB
    @3
    chsscon2
    biimprd
    adantll
    @59
    @57
    cort
    cfv
    #
    @58
    cort
    cfv
    #
    wceq
    #
    @64
    @11
    @57
    @58
    cort
    fveq2
    @62
    @2
    @68
    @11
    wb
    @62
    @2
    wa
    #
    @66
    @8
    @67
    @10
    @62
    @0
    @1
    @66
    @8
    wceq
    @62
    @0
    wa
    #
    @1
    wa
    #
    @66
    @56
    cort
    cfv
    #
    @4
    cin
    #
    @8
    @70
    @56
    cch
    wcel
    #
    @1
    @66
    @73
    wceq
    @62
    @54
    @0
    @74
    @65
    @53
    cA
    chincl
    sylan
    @56
    cB
    chdmj1
    sylan
    @71
    @72
    @7
    @4
    @70
    @72
    @7
    wceq
    @1
    @3
    cA
    chdmm2
    adantr
    ineq1d
    eqtrd
    anasss
    @69
    @67
    @3
    @18
    cort
    cfv
    #
    chj
    co
    #
    @10
    @2
    @62
    @18
    cch
    wcel
    @67
    @76
    wceq
    cA
    cB
    chjcl
    @3
    @18
    chdmm2
    sylan2
    @69
    @75
    @9
    @3
    chj
    @2
    @75
    @9
    wceq
    @62
    cA
    cB
    chdmj1
    adantl
    oveq2d
    eqtrd
    eqeq12d
    ancoms
    syl5ib
    imim12d
    syld
    ex
    com23
    syl5
    ralrimdv
    impbid
    @0
    @46
    @51
    @23
    @13
    wb
    @1
    @47
    @52
    vy
    @6
    @4
    mdbr
    syl2an
    vx
    cA
    cB
    dmdbr
    3bitr4rd
end

include "con0.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "wceq.mm"
include "c0.mm"
include "csuc.mm"
include "oveq2.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "uneq2d.mm"
include "eqeq12d.mm"
include "oa0.mm"
include "un0.mm"
include "syl6eqr.mm"
include "wi.mm"
include "wa.mm"
include "csn.mm"
include "uneq1.mm"
include "unass.mm"
include "wrex.mm"
include "wo.mm"
include "rexun.mm"
include "df-suc.mm"
include "rexeqi.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "velsn.mm"
include "eqeq2d.mm"
include "rexsn.mm"
include "bitr4i.mm"
include "orbi12i.mm"
include "3bitr4i.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "elun.mm"
include "eqriv.mm"
include "uneq2i.mm"
include "eqtr4i.mm"
include "oasuc.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "wlim.mm"
include "wral.mm"
include "ciun.mm"
include "oalim.mm"
include "mpanr1.mm"
include "ancoms.mm"
include "adantr.mm"
include "iuneq2.mm"
include "adantl.mm"
include "iunun.mm"
include "wne.mm"
include "0ellim.mm"
include "ne0i.mm"
include "iunconst.mm"
include "3syl.mm"
include "cuni.mm"
include "limuni.mm"
include "rexeqdv.mm"
include "wex.mm"
include "df-rex.mm"
include "bitri.mm"
include "rexbii.mm"
include "eluni2.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "exbii.mm"
include "rexcom4.mm"
include "syl6rbbr.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "uneq12d.mm"
include "syl5eq.mm"
include "ad2antrr.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "tfinds3.mm"
include "impcom.mm"

theorem oarec
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  assert |- ( ( A e. On /\ B e. On ) -> ( A +o B ) = ( A u. ran ( x e. B |-> ( A +o x ) ) ) )

  proof
    cB
    con0
    wcel
    cA
    con0
    wcel
    #
    cA
    cB
    coa
    co
    #
    cA
    vx
    cB
    cA
    vx
    cv
    #
    coa
    co
    #
    cmpt
    #
    crn
    #
    cun
    #
    wceq
    #
    cA
    vz
    cv
    #
    coa
    co
    #
    cA
    vx
    @8
    @3
    cmpt
    #
    crn
    #
    cun
    #
    wceq
    #
    cA
    c0
    coa
    co
    #
    cA
    c0
    cun
    #
    wceq
    cA
    vw
    cv
    #
    coa
    co
    #
    cA
    vx
    @16
    @3
    cmpt
    #
    crn
    #
    cun
    #
    wceq
    #
    cA
    @16
    csuc
    #
    coa
    co
    #
    cA
    vx
    @22
    @3
    cmpt
    #
    crn
    #
    cun
    #
    wceq
    #
    @7
    @0
    vz
    vw
    cB
    @8
    c0
    wceq
    #
    @9
    @14
    @12
    @15
    @8
    c0
    cA
    coa
    oveq2
    @28
    @11
    c0
    cA
    @28
    @11
    c0
    crn
    c0
    @28
    @10
    c0
    @28
    @10
    vx
    c0
    @3
    cmpt
    c0
    vx
    @8
    c0
    @3
    mpteq1
    vx
    @3
    mpt0
    syl6eq
    rneqd
    rn0
    syl6eq
    uneq2d
    eqeq12d
    @8
    @16
    wceq
    #
    @9
    @17
    @12
    @20
    @8
    @16
    cA
    coa
    oveq2
    @29
    @11
    @19
    cA
    @29
    @10
    @18
    vx
    @8
    @16
    @3
    mpteq1
    rneqd
    uneq2d
    eqeq12d
    @8
    @22
    wceq
    #
    @9
    @23
    @12
    @26
    @8
    @22
    cA
    coa
    oveq2
    @30
    @11
    @25
    cA
    @30
    @10
    @24
    vx
    @8
    @22
    @3
    mpteq1
    rneqd
    uneq2d
    eqeq12d
    @8
    cB
    wceq
    #
    @9
    @1
    @12
    @6
    @8
    cB
    cA
    coa
    oveq2
    @31
    @11
    @5
    cA
    @31
    @10
    @4
    vx
    @8
    cB
    @3
    mpteq1
    rneqd
    uneq2d
    eqeq12d
    @0
    @14
    cA
    @15
    cA
    oa0
    cA
    un0
    syl6eqr
    @0
    @16
    con0
    wcel
    #
    @21
    @27
    wi
    @21
    @27
    @0
    @32
    wa
    #
    @17
    @17
    csn
    #
    cun
    #
    @26
    wceq
    @21
    @35
    @20
    @34
    cun
    #
    @26
    @17
    @20
    @34
    uneq1
    @36
    cA
    @19
    @34
    cun
    #
    cun
    @26
    cA
    @19
    @34
    unass
    @25
    @37
    cA
    vy
    @25
    @37
    vy
    cv
    #
    @3
    wceq
    #
    vx
    @22
    wrex
    #
    @38
    @19
    wcel
    #
    @38
    @34
    wcel
    #
    wo
    #
    @38
    @25
    wcel
    @38
    @37
    wcel
    @39
    vx
    @16
    @16
    csn
    #
    cun
    #
    wrex
    @39
    vx
    @16
    wrex
    #
    @39
    vx
    @44
    wrex
    #
    wo
    @40
    @43
    @39
    vx
    @16
    @44
    rexun
    @39
    vx
    @22
    @45
    @16
    df-suc
    rexeqi
    @41
    @46
    @42
    @47
    @38
    cvv
    wcel
    @41
    @46
    wb
    vy
    vex
    vx
    @16
    @3
    @38
    @18
    cvv
    @18
    eqid
    elrnmpt
    ax-mp
    #
    @42
    @38
    @17
    wceq
    #
    @47
    vy
    @17
    velsn
    @39
    @49
    vx
    @16
    vw
    vex
    @2
    @16
    wceq
    @3
    @17
    @38
    @2
    @16
    cA
    coa
    oveq2
    eqeq2d
    rexsn
    bitr4i
    orbi12i
    3bitr4i
    vx
    @22
    @3
    @38
    @24
    @24
    eqid
    cA
    @2
    coa
    ovex
    #
    elrnmpti
    @38
    @19
    @34
    elun
    3bitr4i
    eqriv
    uneq2i
    eqtr4i
    syl6eq
    @33
    @23
    @35
    @26
    @33
    @23
    @17
    csuc
    @35
    cA
    @16
    oasuc
    @17
    df-suc
    syl6eq
    eqeq1d
    syl5ibr
    expcom
    @8
    wlim
    #
    @0
    @21
    vw
    @8
    wral
    #
    @13
    @51
    @0
    wa
    #
    @52
    wa
    @9
    vw
    @8
    @17
    ciun
    #
    vw
    @8
    @20
    ciun
    #
    @12
    @53
    @9
    @54
    wceq
    #
    @52
    @0
    @51
    @56
    @0
    @8
    cvv
    wcel
    @51
    @56
    vz
    vex
    vw
    cA
    @8
    cvv
    oalim
    mpanr1
    ancoms
    adantr
    @52
    @54
    @55
    wceq
    @53
    vw
    @8
    @17
    @20
    iuneq2
    adantl
    @51
    @55
    @12
    wceq
    @0
    @52
    @51
    @55
    vw
    @8
    cA
    ciun
    #
    vw
    @8
    @19
    ciun
    #
    cun
    @12
    vw
    @8
    cA
    @19
    iunun
    @51
    @57
    cA
    @58
    @11
    @51
    c0
    @8
    wcel
    @8
    c0
    wne
    @57
    cA
    wceq
    @8
    0ellim
    @8
    c0
    ne0i
    vw
    @8
    cA
    iunconst
    3syl
    @51
    vy
    @58
    @11
    @51
    @41
    vw
    @8
    wrex
    #
    @39
    vx
    @8
    wrex
    #
    @38
    @58
    wcel
    @38
    @11
    wcel
    @51
    @60
    @39
    vx
    @8
    cuni
    #
    wrex
    #
    @59
    @51
    @39
    vx
    @8
    @61
    @8
    limuni
    rexeqdv
    @59
    @2
    @16
    wcel
    #
    @39
    wa
    #
    vx
    wex
    #
    vw
    @8
    wrex
    #
    @62
    @41
    @65
    vw
    @8
    @41
    @46
    @65
    @48
    @39
    vx
    @16
    df-rex
    bitri
    rexbii
    @2
    @61
    wcel
    #
    @39
    wa
    #
    vx
    wex
    @64
    vw
    @8
    wrex
    #
    vx
    wex
    @62
    @66
    @68
    @69
    vx
    @68
    @63
    vw
    @8
    wrex
    #
    @39
    wa
    @69
    @67
    @70
    @39
    vw
    @2
    @8
    eluni2
    anbi1i
    @63
    @39
    vw
    @8
    r19.41v
    bitr4i
    exbii
    @39
    vx
    @61
    df-rex
    @64
    vw
    vx
    @8
    rexcom4
    3bitr4i
    bitr4i
    syl6rbbr
    vw
    @38
    @8
    @19
    eliun
    vx
    @8
    @3
    @38
    @10
    @10
    eqid
    @50
    elrnmpti
    3bitr4g
    eqrdv
    uneq12d
    syl5eq
    ad2antrr
    3eqtrd
    exp31
    tfinds3
    impcom
end

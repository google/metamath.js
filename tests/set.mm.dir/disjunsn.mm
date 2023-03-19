include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "wdisj.mm"
include "cv.mm"
include "wceq.mm"
include "csb.mm"
include "cin.mm"
include "c0.mm"
include "wo.mm"
include "wral.mm"
include "ciun.mm"
include "wb.mm"
include "disjors.mm"
include "eqeq1.mm"
include "csbeq1.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "ralbidv.mm"
include "ralunsn.mm"
include "syl5bb.mm"
include "eqeq2.mm"
include "ineq2d.mm"
include "eqid.mm"
include "orci.mm"
include "biantru.mm"
include "syl6bbr.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "r19.26.mm"
include "anbi1i.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "adantr.mm"
include "orcom.mm"
include "ralbii.mm"
include "wrex.mm"
include "r19.30.mm"
include "risset.mm"
include "biorf.mm"
include "sylnbi.mm"
include "adantl.mm"
include "syl5ibr.mm"
include "syl5bir.mm"
include "olc.mm"
include "ralimi.mm"
include "impbid1.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfin.mm"
include "nfeq1.mm"
include "csbeq1a.mm"
include "cbvral.mm"
include "a1i.mm"
include "wss.mm"
include "ss0b.mm"
include "iunss.mm"
include "iunin1.mm"
include "eqeq1i.mm"
include "3bitr3ri.mm"
include "bitri.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "3bitr4d.mm"
include "bitr4d.mm"
include "anbi2d.mm"
include "clel5.mm"
include "incom.mm"
include "anass.mm"
include "anidm.mm"
include "anbi2i.mm"

theorem disjunsn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  assume disjunsn.s: |- ( x = M -> B = C )

  disjoint A x
  disjoint C x
  disjoint M x
  disjoint V x
  disjoint i j
  disjoint i x
  disjoint A i
  disjoint j x
  disjoint A j
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint M i
  disjoint M j
  disjoint V i
  disjoint V j
  assert |- ( ( M e. V /\ -. M e. A ) -> ( Disj_ x e. ( A u. { M } ) B <-> ( Disj_ x e. A B /\ ( U_ x e. A B i^i C ) = (/) ) ) )

  proof
    cM
    cV
    wcel
    #
    cM
    cA
    wcel
    #
    wn
    #
    wa
    #
    vx
    cA
    cM
    csn
    cun
    #
    cB
    wdisj
    #
    vx
    cA
    cB
    wdisj
    #
    vi
    cv
    #
    cM
    wceq
    #
    vx
    @7
    cB
    csb
    #
    vx
    cM
    cB
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vi
    cA
    wral
    #
    wa
    #
    cM
    vj
    cv
    #
    wceq
    #
    @10
    vx
    @16
    cB
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vj
    cA
    wral
    #
    wa
    #
    @6
    vx
    cA
    cB
    ciun
    cC
    cin
    #
    c0
    wceq
    #
    wa
    #
    @0
    @5
    @23
    wb
    @2
    @0
    @5
    @7
    @16
    wceq
    #
    @9
    @18
    cin
    #
    c0
    wceq
    #
    wo
    #
    vj
    cA
    wral
    #
    @13
    wa
    #
    vi
    cA
    wral
    #
    @22
    wa
    #
    @23
    @0
    @5
    @30
    vj
    @4
    wral
    #
    vi
    cA
    wral
    #
    @21
    vj
    @4
    wral
    #
    wa
    #
    @34
    @5
    @35
    vi
    @4
    wral
    @0
    @38
    vx
    @4
    cB
    vi
    vj
    disjors
    @35
    @37
    vi
    cA
    cM
    cV
    @8
    @30
    @21
    vj
    @4
    @8
    @27
    @17
    @29
    @20
    @7
    cM
    @16
    eqeq1
    @8
    @28
    @19
    c0
    @8
    @9
    @10
    @18
    vx
    @7
    cM
    cB
    csbeq1
    ineq1d
    eqeq1d
    orbi12d
    ralbidv
    ralunsn
    syl5bb
    @0
    @36
    @33
    @37
    @22
    @0
    @35
    @32
    vi
    cA
    @30
    @13
    vj
    cA
    cM
    cV
    @16
    cM
    wceq
    #
    @27
    @8
    @29
    @12
    @16
    cM
    @7
    eqeq2
    @39
    @28
    @11
    c0
    @39
    @18
    @10
    @9
    vx
    @16
    cM
    cB
    csbeq1
    #
    ineq2d
    eqeq1d
    orbi12d
    ralunsn
    ralbidv
    @0
    @37
    @22
    cM
    cM
    wceq
    #
    @10
    @10
    cin
    #
    c0
    wceq
    #
    wo
    #
    wa
    @22
    @21
    @44
    vj
    cA
    cM
    cV
    @39
    @17
    @41
    @20
    @43
    @16
    cM
    cM
    eqeq2
    @39
    @19
    @42
    c0
    @39
    @18
    @10
    @10
    @40
    ineq2d
    eqeq1d
    orbi12d
    ralunsn
    @44
    @22
    @41
    @43
    cM
    eqid
    orci
    biantru
    syl6bbr
    anbi12d
    bitrd
    @33
    @15
    @22
    @33
    @31
    vi
    cA
    wral
    #
    @14
    wa
    @15
    @31
    @13
    vi
    cA
    r19.26
    @6
    @45
    @14
    vx
    cA
    cB
    vi
    vj
    disjors
    anbi1i
    bitr4i
    anbi1i
    syl6bb
    adantr
    @3
    @23
    @26
    @25
    wa
    #
    @26
    @3
    @15
    @26
    @22
    @25
    @3
    @14
    @25
    @6
    @3
    @14
    @12
    vi
    cA
    wral
    #
    @25
    @3
    @14
    @47
    @14
    @12
    @8
    wo
    #
    vi
    cA
    wral
    #
    @3
    @47
    @48
    @13
    vi
    cA
    @12
    @8
    orcom
    ralbii
    @49
    @47
    @3
    @47
    @8
    vi
    cA
    wrex
    #
    wo
    #
    @12
    @8
    vi
    cA
    r19.30
    @3
    @47
    @50
    @47
    wo
    #
    @51
    @2
    @47
    @52
    wb
    #
    @0
    @1
    @50
    @53
    vi
    cM
    cA
    risset
    @50
    @47
    biorf
    sylnbi
    adantl
    @50
    @47
    orcom
    syl6bb
    syl5ibr
    syl5bir
    @12
    @13
    vi
    cA
    @12
    @8
    olc
    ralimi
    impbid1
    @0
    @25
    @47
    wb
    @2
    @0
    cB
    cC
    cin
    #
    c0
    wceq
    #
    vx
    cA
    wral
    #
    @9
    cC
    cin
    #
    c0
    wceq
    #
    vi
    cA
    wral
    #
    @25
    @47
    @56
    @59
    wb
    @0
    @55
    @58
    vx
    vi
    cA
    @55
    vi
    nfv
    vx
    @57
    c0
    vx
    @9
    cC
    vx
    @7
    cB
    nfcsb1v
    vx
    cC
    nfcv
    #
    nfin
    nfeq1
    vx
    cv
    #
    @7
    wceq
    #
    @54
    @57
    c0
    @62
    cB
    @9
    cC
    vx
    @7
    cB
    csbeq1a
    ineq1d
    eqeq1d
    cbvral
    a1i
    @25
    @56
    wb
    @0
    @25
    @54
    c0
    wss
    #
    vx
    cA
    wral
    #
    @56
    vx
    cA
    @54
    ciun
    #
    c0
    wss
    @65
    c0
    wceq
    @64
    @25
    @65
    ss0b
    vx
    cA
    @54
    c0
    iunss
    @65
    @24
    c0
    vx
    cA
    cC
    cB
    iunin1
    eqeq1i
    3bitr3ri
    @63
    @55
    vx
    cA
    @54
    ss0b
    ralbii
    bitri
    a1i
    #
    @0
    @12
    @58
    vi
    cA
    @0
    @11
    @57
    c0
    @0
    @10
    cC
    @9
    vx
    cM
    cB
    cC
    cV
    @0
    vx
    cC
    nfcvd
    disjunsn.s
    csbiegf
    #
    ineq2d
    eqeq1d
    ralbidv
    3bitr4d
    adantr
    bitr4d
    anbi2d
    @3
    @22
    @20
    vj
    cA
    wral
    #
    @25
    @3
    @22
    @68
    @22
    @20
    @17
    wo
    #
    vj
    cA
    wral
    #
    @3
    @68
    @69
    @21
    vj
    cA
    @20
    @17
    orcom
    ralbii
    @70
    @68
    @3
    @68
    @17
    vj
    cA
    wrex
    #
    wo
    #
    @20
    @17
    vj
    cA
    r19.30
    @3
    @68
    @71
    @68
    wo
    #
    @72
    @2
    @68
    @73
    wb
    #
    @0
    @1
    @71
    @74
    vj
    cA
    cM
    clel5
    @71
    @68
    biorf
    sylnbi
    adantl
    @71
    @68
    orcom
    syl6bb
    syl5ibr
    syl5bir
    @20
    @21
    vj
    cA
    @20
    @17
    olc
    ralimi
    impbid1
    @0
    @25
    @68
    wb
    @2
    @0
    @56
    cC
    @18
    cin
    #
    c0
    wceq
    #
    vj
    cA
    wral
    #
    @25
    @68
    @0
    @56
    @18
    cC
    cin
    #
    c0
    wceq
    #
    vj
    cA
    wral
    #
    @77
    @56
    @80
    wb
    @0
    @55
    @79
    vx
    vj
    cA
    @55
    vj
    nfv
    vx
    @78
    c0
    vx
    @18
    cC
    vx
    @16
    cB
    nfcsb1v
    @60
    nfin
    nfeq1
    @61
    @16
    wceq
    #
    @54
    @78
    c0
    @81
    cB
    @18
    cC
    vx
    @16
    cB
    csbeq1a
    ineq1d
    eqeq1d
    cbvral
    a1i
    @79
    @76
    vj
    cA
    @78
    @75
    c0
    @18
    cC
    incom
    eqeq1i
    ralbii
    syl6bb
    @66
    @0
    @20
    @76
    vj
    cA
    @0
    @19
    @75
    c0
    @0
    @10
    cC
    @18
    @67
    ineq1d
    eqeq1d
    ralbidv
    3bitr4d
    adantr
    bitr4d
    anbi12d
    @46
    @6
    @25
    @25
    wa
    #
    wa
    @26
    @6
    @25
    @25
    anass
    @82
    @25
    @6
    @25
    anidm
    anbi2i
    bitri
    syl6bb
    bitrd
end

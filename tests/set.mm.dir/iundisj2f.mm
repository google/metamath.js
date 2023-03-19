include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "ciun.mm"
include "cdif.mm"
include "wdisj.mm"
include "weq.mm"
include "csb.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wtru.mm"
include "wcel.mm"
include "wa.mm"
include "tru.mm"
include "eqeq12.mm"
include "csbeq1.mm"
include "ineqan12d.mm"
include "eqeq1d.mm"
include "orbi12d.mm"
include "equcom.mm"
include "syl6bb.mm"
include "incom.mm"
include "syl6eq.mm"
include "cr.mm"
include "wss.mm"
include "nnssre.mm"
include "a1i.mm"
include "biidd.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wn.mm"
include "wne.mm"
include "nesym.mm"
include "clt.mm"
include "wb.mm"
include "nnre.mm"
include "id.mm"
include "leltne.mm"
include "syl3an.mm"
include "wi.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfiun.mm"
include "nfdif.mm"
include "csbeq1a.mm"
include "oveq2.mm"
include "iuneq1d.mm"
include "difeq12d.mm"
include "csbief.mm"
include "ineq12i.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "simp1.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "simp2.mm"
include "nnzd.mm"
include "simp3.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "nfcsb.mm"
include "csbhypf.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "ssiun2sf.mm"
include "syl.mm"
include "ssdifssd.mm"
include "ssrin.mm"
include "syl5eqss.mm"
include "disjdif.mm"
include "sseq0.mm"
include "sylancl.mm"
include "3expia.mm"
include "3adant3.mm"
include "sylbird.mm"
include "syl5bir.mm"
include "orrd.mm"
include "adantl.mm"
include "wlogle.mm"
include "mpan.mm"
include "rgen2a.mm"
include "disjors.mm"
include "mpbir.mm"

theorem iundisj2f
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume iundisjf.1: |- F/_ k A
  assume iundisjf.2: |- F/_ n B
  assume iundisjf.3: |- ( n = k -> A = B )

  disjoint k n
  disjoint a b
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint k m
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A a
  disjoint A b
  disjoint A m
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B m
  disjoint B x
  disjoint B y
  assert |- Disj_ n e. NN ( A \ U_ k e. ( 1 ..^ n ) B )

  proof
    vn
    cn
    cA
    vk
    c1
    vn
    cv
    #
    cfzo
    co
    #
    cB
    ciun
    #
    cdif
    #
    wdisj
    vx
    vy
    weq
    #
    vn
    vx
    cv
    #
    @3
    csb
    #
    vn
    vy
    cv
    #
    @3
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vy
    cn
    wral
    vx
    cn
    wral
    @11
    vx
    vy
    cn
    wtru
    @5
    cn
    wcel
    #
    @7
    cn
    wcel
    #
    wa
    #
    @11
    tru
    wtru
    va
    vb
    weq
    #
    vn
    va
    cv
    #
    @3
    csb
    #
    vn
    vb
    cv
    #
    @3
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    @11
    @11
    vx
    vy
    va
    vb
    cn
    va
    vx
    weq
    #
    vb
    vy
    weq
    #
    wa
    #
    @15
    @4
    @21
    @10
    @16
    @5
    @18
    @7
    eqeq12
    @24
    @20
    @9
    c0
    @22
    @23
    @17
    @6
    @19
    @8
    vn
    @16
    @5
    @3
    csbeq1
    vn
    @18
    @7
    @3
    csbeq1
    ineqan12d
    eqeq1d
    orbi12d
    va
    vy
    weq
    #
    vb
    vx
    weq
    #
    wa
    #
    @15
    @4
    @21
    @10
    @27
    @15
    vy
    vx
    weq
    @4
    @16
    @7
    @18
    @5
    eqeq12
    vy
    vx
    equcom
    syl6bb
    @27
    @20
    @9
    c0
    @27
    @20
    @8
    @6
    cin
    @9
    @25
    @26
    @17
    @8
    @19
    @6
    vn
    @16
    @7
    @3
    csbeq1
    vn
    @18
    @5
    @3
    csbeq1
    ineqan12d
    @8
    @6
    incom
    syl6eq
    eqeq1d
    orbi12d
    cn
    cr
    wss
    wtru
    nnssre
    a1i
    wtru
    @14
    wa
    @11
    biidd
    @12
    @13
    @5
    @7
    cle
    wbr
    #
    w3a
    #
    @11
    wtru
    @29
    @4
    @10
    @4
    wn
    @7
    @5
    wne
    #
    @29
    @10
    @7
    @5
    nesym
    @29
    @30
    @5
    @7
    clt
    wbr
    #
    @10
    @12
    @5
    cr
    wcel
    @13
    @7
    cr
    wcel
    @28
    @28
    @31
    @30
    wb
    @5
    nnre
    @7
    nnre
    @28
    id
    @5
    @7
    leltne
    syl3an
    @12
    @13
    @31
    @10
    wi
    @28
    @12
    @13
    @31
    @10
    @12
    @13
    @31
    w3a
    #
    @9
    vk
    c1
    @7
    cfzo
    co
    #
    cB
    ciun
    #
    vn
    @7
    cA
    csb
    #
    @34
    cdif
    #
    cin
    #
    wss
    @37
    c0
    wceq
    @10
    @32
    @9
    vn
    @5
    cA
    csb
    #
    vk
    c1
    @5
    cfzo
    co
    #
    cB
    ciun
    #
    cdif
    #
    @36
    cin
    #
    @37
    @6
    @41
    @8
    @36
    vn
    @5
    @3
    @41
    vx
    vex
    vn
    @38
    @40
    vn
    @5
    cA
    nfcsb1v
    vk
    vn
    @39
    cB
    vn
    @39
    nfcv
    iundisjf.2
    nfiun
    nfdif
    vn
    vx
    weq
    #
    cA
    @38
    @2
    @40
    vn
    @5
    cA
    csbeq1a
    @43
    vk
    @1
    @39
    cB
    @0
    @5
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    csbief
    vn
    @7
    @3
    @36
    vy
    vex
    vn
    @35
    @34
    vn
    @7
    cA
    nfcsb1v
    vk
    vn
    @33
    cB
    vn
    @33
    nfcv
    iundisjf.2
    nfiun
    nfdif
    vn
    vy
    weq
    #
    cA
    @35
    @2
    @34
    vn
    @7
    cA
    csbeq1a
    @44
    vk
    @1
    @33
    cB
    @0
    @7
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    csbief
    ineq12i
    @32
    @41
    @34
    wss
    @42
    @37
    wss
    @32
    @38
    @34
    @40
    @32
    @5
    @33
    wcel
    #
    @38
    @34
    wss
    @32
    @5
    c1
    cuz
    cfv
    #
    wcel
    @7
    cz
    wcel
    @31
    @45
    @32
    @5
    cn
    @46
    @12
    @13
    @31
    simp1
    nnuz
    syl6eleq
    @32
    @7
    @12
    @13
    @31
    simp2
    nnzd
    @12
    @13
    @31
    simp3
    @5
    c1
    @7
    elfzo2
    syl3anbrc
    vk
    @33
    cB
    @5
    @38
    vk
    @33
    nfcv
    vk
    @5
    nfcv
    #
    vk
    vn
    @5
    cA
    @47
    iundisjf.1
    nfcsb
    vk
    vx
    weq
    @38
    cB
    @38
    cB
    wceq
    vx
    vk
    vn
    vx
    vk
    cv
    #
    cA
    cB
    vn
    @48
    nfcv
    iundisjf.2
    iundisjf.3
    csbhypf
    equcoms
    eqcomd
    ssiun2sf
    syl
    ssdifssd
    @41
    @34
    @36
    ssrin
    syl
    syl5eqss
    @34
    @35
    disjdif
    @9
    @37
    sseq0
    sylancl
    3expia
    3adant3
    sylbird
    syl5bir
    orrd
    adantl
    wlogle
    mpan
    rgen2a
    vn
    cn
    @3
    vx
    vy
    disjors
    mpbir
end

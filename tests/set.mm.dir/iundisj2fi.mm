include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
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
include "cn.mm"
include "fzossnn.mm"
include "nnssre.mm"
include "sstri.mm"
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
include "sseli.mm"
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
include "sseldi.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "simp2.mm"
include "nnzd.mm"
include "simp3.mm"
include "elfzo2.mm"
include "syl3anbrc.mm"
include "csbhypf.mm"
include "equcoms.mm"
include "eqcomd.mm"
include "ssiun2s.mm"
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

theorem iundisj2fi
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume iundisj2fi.0: |- F/_ n B
  assume iundisj2fi.1: |- ( n = k -> A = B )

  disjoint k n
  disjoint N k
  disjoint N n
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint N a
  disjoint b k
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint N b
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint A a
  disjoint A b
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B b
  disjoint B x
  disjoint B y
  assert |- Disj_ n e. ( 1 ..^ N ) ( A \ U_ k e. ( 1 ..^ n ) B )

  proof
    vn
    c1
    cN
    cfzo
    co
    #
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
    @4
    csb
    #
    vn
    vy
    cv
    #
    @4
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
    @0
    wral
    vx
    @0
    wral
    @12
    vx
    vy
    @0
    wtru
    @6
    @0
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    #
    @12
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
    @4
    csb
    #
    vn
    vb
    cv
    #
    @4
    csb
    #
    cin
    #
    c0
    wceq
    #
    wo
    @12
    @12
    vx
    vy
    va
    vb
    @0
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
    @16
    @5
    @22
    @11
    @17
    @6
    @19
    @8
    eqeq12
    @25
    @21
    @10
    c0
    @23
    @24
    @18
    @7
    @20
    @9
    vn
    @17
    @6
    @4
    csbeq1
    vn
    @19
    @8
    @4
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
    @16
    @5
    @22
    @11
    @28
    @16
    vy
    vx
    weq
    @5
    @17
    @8
    @19
    @6
    eqeq12
    vy
    vx
    equcom
    syl6bb
    @28
    @21
    @10
    c0
    @28
    @21
    @9
    @7
    cin
    @10
    @26
    @27
    @18
    @9
    @20
    @7
    vn
    @17
    @8
    @4
    csbeq1
    vn
    @19
    @6
    @4
    csbeq1
    ineqan12d
    @9
    @7
    incom
    syl6eq
    eqeq1d
    orbi12d
    @0
    cr
    wss
    wtru
    @0
    cn
    cr
    cN
    fzossnn
    #
    nnssre
    sstri
    #
    a1i
    wtru
    @15
    wa
    @12
    biidd
    @13
    @14
    @6
    @8
    cle
    wbr
    #
    w3a
    #
    @12
    wtru
    @32
    @5
    @11
    @5
    wn
    @8
    @6
    wne
    #
    @32
    @11
    @8
    @6
    nesym
    @32
    @33
    @6
    @8
    clt
    wbr
    #
    @11
    @13
    @6
    cr
    wcel
    @14
    @8
    cr
    wcel
    @31
    @31
    @34
    @33
    wb
    @0
    cr
    @6
    @30
    sseli
    @0
    cr
    @8
    @30
    sseli
    @31
    id
    @6
    @8
    leltne
    syl3an
    @13
    @14
    @34
    @11
    wi
    @31
    @13
    @14
    @34
    @11
    @13
    @14
    @34
    w3a
    #
    @10
    vk
    c1
    @8
    cfzo
    co
    #
    cB
    ciun
    #
    vn
    @8
    cA
    csb
    #
    @37
    cdif
    #
    cin
    #
    wss
    @40
    c0
    wceq
    @11
    @35
    @10
    vn
    @6
    cA
    csb
    #
    vk
    c1
    @6
    cfzo
    co
    #
    cB
    ciun
    #
    cdif
    #
    @39
    cin
    #
    @40
    @7
    @44
    @9
    @39
    vn
    @6
    @4
    @44
    vx
    vex
    vn
    @41
    @43
    vn
    @6
    cA
    nfcsb1v
    vk
    vn
    @42
    cB
    vn
    @42
    nfcv
    iundisj2fi.0
    nfiun
    nfdif
    vn
    vx
    weq
    #
    cA
    @41
    @3
    @43
    vn
    @6
    cA
    csbeq1a
    @46
    vk
    @2
    @42
    cB
    @1
    @6
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    csbief
    vn
    @8
    @4
    @39
    vy
    vex
    vn
    @38
    @37
    vn
    @8
    cA
    nfcsb1v
    vk
    vn
    @36
    cB
    vn
    @36
    nfcv
    iundisj2fi.0
    nfiun
    nfdif
    vn
    vy
    weq
    #
    cA
    @38
    @3
    @37
    vn
    @8
    cA
    csbeq1a
    @47
    vk
    @2
    @36
    cB
    @1
    @8
    c1
    cfzo
    oveq2
    iuneq1d
    difeq12d
    csbief
    ineq12i
    @35
    @44
    @37
    wss
    @45
    @40
    wss
    @35
    @41
    @37
    @43
    @35
    @6
    @36
    wcel
    #
    @41
    @37
    wss
    @35
    @6
    c1
    cuz
    cfv
    #
    wcel
    @8
    cz
    wcel
    @34
    @48
    @35
    @6
    cn
    @49
    @35
    @0
    cn
    @6
    @29
    @13
    @14
    @34
    simp1
    sseldi
    nnuz
    syl6eleq
    @35
    @8
    @35
    @0
    cn
    @8
    @29
    @13
    @14
    @34
    simp2
    sseldi
    nnzd
    @13
    @14
    @34
    simp3
    @6
    c1
    @8
    elfzo2
    syl3anbrc
    vk
    @36
    cB
    @6
    @41
    vk
    vx
    weq
    @41
    cB
    @41
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
    @50
    nfcv
    iundisj2fi.0
    iundisj2fi.1
    csbhypf
    equcoms
    eqcomd
    ssiun2s
    syl
    ssdifssd
    @44
    @37
    @39
    ssrin
    syl
    syl5eqss
    @37
    @38
    disjdif
    @10
    @40
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
    @0
    @4
    vx
    vy
    disjors
    mpbir
end

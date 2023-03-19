include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cr.mm"
include "cdvn.mm"
include "cmul.mm"
include "csu.mm"
include "c1.mm"
include "cmin.mm"
include "cfa.mm"
include "cdiv.mm"
include "cz.mm"
include "cfn.mm"
include "wcel.mm"
include "fzfi.mm"
include "xpfi.mm"
include "mp2an.mm"
include "a1i.mm"
include "cn.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "faccld.mm"
include "nncnd.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "xp1st.mm"
include "elfznn0.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "zcnd.mm"
include "cc.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "reopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "eleqtri.mm"
include "xp2nd.mm"
include "etransclem33.mm"
include "nn0red.mm"
include "mulcld.mm"
include "nnne0d.mm"
include "fsumdivc.mm"
include "wne.mm"
include "divassd.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cif.mm"
include "cexp.mm"
include "etransclem5.mm"
include "etransclem11.mm"
include "etransclem37.mm"
include "wb.mm"
include "nnzd.mm"
include "nn0zd.mm"
include "etransclem42.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "zmulcld.mm"
include "eqeltrd.mm"
include "fsumzcl.mm"
include "syl5eqel.mm"

theorem etransclem45
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cR: class R
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cM: class M
  let vc: setvar c
  let vd: setvar d
  let vn: setvar n
  let vm: setvar m
  let vy: setvar y
  assume etransclem45.p: |- ( ph -> P e. NN )
  assume etransclem45.m: |- ( ph -> M e. NN0 )
  assume etransclem45.f: |- F = ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem45.a: |- ( ph -> A : NN0 --> ZZ )
  assume etransclem45.k: |- K = ( sum_ k e. ( ( 0 ... M ) X. ( 0 ... R ) ) ( ( A ` ( 1st ` k ) ) x. ( ( ( RR Dn F ) ` ( 2nd ` k ) ) ` ( 1st ` k ) ) ) / ( ! ` ( P - 1 ) ) )

  disjoint M j
  disjoint M k
  disjoint M x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint R j
  disjoint R k
  disjoint R x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint M c
  disjoint M d
  disjoint M n
  disjoint c d
  disjoint c j
  disjoint c k
  disjoint c n
  disjoint c x
  disjoint d j
  disjoint d k
  disjoint d n
  disjoint d x
  disjoint j n
  disjoint k n
  disjoint n x
  disjoint M m
  disjoint c m
  disjoint d m
  disjoint j m
  disjoint m n
  disjoint m x
  disjoint P c
  disjoint P n
  disjoint P y
  disjoint c y
  disjoint j y
  disjoint k y
  disjoint n y
  disjoint x y
  disjoint R c
  disjoint R n
  disjoint c ph
  disjoint n ph
  assert |- ( ph -> K e. ZZ )

  proof
    wph
    cK
    cc0
    cM
    cfz
    co
    #
    cc0
    cR
    cfz
    co
    #
    cxp
    #
    vk
    cv
    #
    c1st
    cfv
    #
    cA
    cfv
    #
    @4
    @3
    c2nd
    cfv
    #
    cr
    cF
    cdvn
    co
    cfv
    #
    cfv
    #
    cmul
    co
    #
    vk
    csu
    cP
    c1
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cz
    etransclem45.k
    wph
    @12
    @2
    @9
    @11
    cdiv
    co
    #
    vk
    csu
    cz
    wph
    @2
    @9
    @11
    vk
    @2
    cfn
    wcel
    #
    wph
    @0
    cfn
    wcel
    @1
    cfn
    wcel
    @14
    cc0
    cM
    fzfi
    cc0
    cR
    fzfi
    @0
    @1
    xpfi
    mp2an
    a1i
    #
    wph
    @11
    wph
    @10
    wph
    cP
    cn
    wcel
    #
    @10
    cn0
    wcel
    etransclem45.p
    cP
    nnm1nn0
    syl
    faccld
    #
    nncnd
    #
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @5
    @8
    @20
    @5
    @20
    cn0
    cz
    @4
    cA
    wph
    cn0
    cz
    cA
    wf
    @19
    etransclem45.a
    adantr
    @19
    @4
    cn0
    wcel
    #
    wph
    @19
    @4
    @0
    wcel
    #
    @21
    @3
    @0
    @1
    xp1st
    #
    @4
    cM
    elfznn0
    syl
    adantl
    #
    ffvelrnd
    #
    zcnd
    #
    @20
    cr
    cc
    @4
    @7
    @20
    vx
    cP
    cr
    vj
    cF
    cM
    @6
    cr
    cr
    cr
    cc
    cpr
    wcel
    @20
    reelprrecn
    a1i
    #
    cr
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    wcel
    @20
    cr
    cioo
    crn
    ctg
    cfv
    @29
    reopn
    @28
    @28
    eqid
    tgioo2
    eleqtri
    a1i
    #
    wph
    @16
    @19
    etransclem45.p
    adantr
    #
    wph
    cM
    cn0
    wcel
    @19
    etransclem45.m
    adantr
    #
    etransclem45.f
    @19
    @6
    cn0
    wcel
    #
    wph
    @19
    @6
    @1
    wcel
    @33
    @3
    @0
    @1
    xp2nd
    @6
    cR
    elfznn0
    syl
    adantl
    #
    etransclem33
    @20
    @4
    @24
    nn0red
    #
    ffvelrnd
    #
    mulcld
    wph
    @11
    @17
    nnne0d
    #
    fsumdivc
    wph
    @2
    @13
    vk
    @15
    @20
    @13
    @5
    @8
    @11
    cdiv
    co
    #
    cmul
    co
    cz
    @20
    @5
    @8
    @11
    @26
    @36
    wph
    @11
    cc
    wcel
    @19
    @18
    adantr
    wph
    @11
    cc0
    wne
    #
    @19
    @37
    adantr
    #
    divassd
    @20
    @5
    @38
    @25
    @20
    @11
    @8
    cdvds
    wbr
    #
    @38
    cz
    wcel
    #
    @20
    vx
    vm
    cn0
    @0
    @3
    vd
    cv
    cfv
    vk
    csu
    vm
    cv
    #
    wceq
    vd
    cc0
    @43
    cfz
    co
    @0
    cmap
    co
    crab
    cmpt
    cP
    cr
    vj
    vn
    cF
    vk
    @0
    vy
    cr
    vy
    cv
    @3
    cmin
    co
    @3
    cc0
    wceq
    @10
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    @4
    cM
    @6
    cr
    vc
    @27
    @30
    @31
    @32
    etransclem45.f
    @34
    vy
    vx
    cP
    vk
    vj
    cM
    cr
    etransclem5
    vk
    vj
    vn
    vm
    cM
    vd
    vc
    etransclem11
    @19
    @22
    wph
    @23
    adantl
    @35
    etransclem37
    @20
    @11
    cz
    wcel
    #
    @39
    @8
    cz
    wcel
    @41
    @42
    wb
    wph
    @44
    @19
    wph
    @11
    @17
    nnzd
    adantr
    @40
    @20
    vx
    cP
    cr
    vj
    cF
    @4
    cM
    @6
    cr
    @27
    @30
    @31
    @32
    etransclem45.f
    @34
    @35
    @20
    @4
    @24
    nn0zd
    etransclem42
    @11
    @8
    dvdsval2
    syl3anc
    mpbid
    zmulcld
    eqeltrd
    fsumzcl
    eqeltrd
    syl5eqel
end

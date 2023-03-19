include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cmul.mm"
include "cc.mm"
include "c1.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "mulid2.mm"
include "adantl.mm"
include "1cnd.mm"
include "adantr.mm"
include "cz.mm"
include "cif.mm"
include "iftrue.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "wn.mm"
include "iffalse.mm"
include "ax-1cn.mm"
include "syl6eqel.mm"
include "pm2.61d1.mm"
include "fmptd.mm"
include "uzssz.mm"
include "sseldi.mm"
include "ffvelrnd.mm"
include "cmin.mm"
include "cfz.mm"
include "cdif.mm"
include "elfzelz.mm"
include "caddc.mm"
include "simplr.mm"
include "zcnd.mm"
include "npcand.mm"
include "fveq2d.mm"
include "sseqtr4d.mm"
include "fznuz.mm"
include "ssneldd.mm"
include "eldifd.mm"
include "weq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "eldifi.mm"
include "eldifn.mm"
include "syl.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "vtoclga.mm"
include "seqid.mm"

theorem prodrblem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let vn: setvar n
  assume prodmo.1: |- F = ( k e. ZZ |-> if ( k e. A , B , 1 ) )
  assume prodmo.2: |- ( ( ph /\ k e. A ) -> B e. CC )
  assume prodrb.3: |- ( ph -> N e. ( ZZ>= ` M ) )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint A n
  disjoint k n
  disjoint F n
  disjoint n ph
  disjoint M n
  disjoint N n
  assert |- ( ( ph /\ A C_ ( ZZ>= ` N ) ) -> ( seq M ( x. , F ) |` ( ZZ>= ` N ) ) = seq N ( x. , F ) )

  proof
    wph
    cA
    cN
    cuz
    cfv
    #
    wss
    #
    wa
    #
    vn
    cmul
    cc
    cF
    cM
    cN
    c1
    vn
    cv
    #
    cc
    wcel
    c1
    @3
    cmul
    co
    @3
    wceq
    @2
    @3
    mulid2
    adantl
    @2
    1cnd
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    @1
    prodrb.3
    adantr
    wph
    cN
    cF
    cfv
    cc
    wcel
    @1
    wph
    cz
    cc
    cN
    cF
    wph
    vk
    cz
    vk
    cv
    #
    cA
    wcel
    #
    cB
    c1
    cif
    #
    cc
    cF
    wph
    @5
    cz
    wcel
    #
    wa
    #
    @6
    @7
    cc
    wcel
    #
    @9
    @6
    @10
    @9
    @6
    wa
    @7
    cB
    cc
    @6
    @7
    cB
    wceq
    @9
    @6
    cB
    c1
    iftrue
    adantl
    wph
    @6
    cB
    cc
    wcel
    @8
    prodmo.2
    adantlr
    eqeltrd
    ex
    @6
    wn
    #
    @7
    c1
    cc
    @6
    cB
    c1
    iffalse
    #
    ax-1cn
    syl6eqel
    pm2.61d1
    prodmo.1
    fmptd
    wph
    @4
    cz
    cN
    cM
    uzssz
    prodrb.3
    sseldi
    #
    ffvelrnd
    adantr
    @2
    @3
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @3
    cz
    cA
    cdif
    #
    wcel
    @3
    cF
    cfv
    #
    c1
    wceq
    #
    @16
    @3
    cz
    cA
    @15
    @3
    cz
    wcel
    @2
    @3
    cM
    @14
    elfzelz
    adantl
    @16
    cA
    @14
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @3
    @16
    cA
    @0
    @21
    wph
    @1
    @15
    simplr
    @16
    @20
    cN
    cuz
    @16
    cN
    c1
    @2
    cN
    cc
    wcel
    #
    @15
    wph
    @22
    @1
    wph
    cN
    @13
    zcnd
    adantr
    adantr
    @16
    1cnd
    npcand
    fveq2d
    sseqtr4d
    @15
    @3
    @21
    wcel
    wn
    @2
    @3
    cM
    @14
    fznuz
    adantl
    ssneldd
    eldifd
    @5
    cF
    cfv
    #
    c1
    wceq
    @19
    vk
    @3
    @17
    vk
    vn
    weq
    @23
    @18
    c1
    @5
    @3
    cF
    fveq2
    eqeq1d
    @5
    @17
    wcel
    #
    @23
    @7
    c1
    @24
    @8
    @10
    @23
    @7
    wceq
    @5
    cz
    cA
    eldifi
    @24
    @7
    c1
    cc
    @24
    @11
    @7
    c1
    wceq
    @5
    cz
    cA
    eldifn
    @12
    syl
    #
    ax-1cn
    syl6eqel
    vk
    cz
    @7
    cc
    cF
    prodmo.1
    fvmpt2
    syl2anc
    @25
    eqtrd
    vtoclga
    syl
    seqid
end

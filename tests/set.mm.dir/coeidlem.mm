include "cc.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "ccoe.mm"
include "cn0.mm"
include "csn.mm"
include "cun.mm"
include "cmap.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "wss.mm"
include "cply.mm"
include "plybss.mm"
include "syl.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpbid.mm"
include "fssd.mm"
include "coeeq.mm"
include "syl5req.mm"
include "adantr.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "cuz.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "cdgr.mm"
include "dgrcl.mm"
include "syl5eqel.mm"
include "nn0zd.mm"
include "c1.mm"
include "caddc.mm"
include "cima.mm"
include "imaeq1d.mm"
include "eqtr3d.mm"
include "dgrlb.mm"
include "syl3anc.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "elfznn0.mm"
include "plyssc.mm"
include "sseldi.mm"
include "coef3.mm"
include "ffvelrnda.mm"
include "expcl.mm"
include "adantll.mm"
include "mulcld.mm"
include "sylan2.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "wne.mm"
include "wi.mm"
include "eldifi.mm"
include "dgrub.mm"
include "3expia.mm"
include "syl2an.mm"
include "elfzuz.mm"
include "elfz5.mm"
include "syl2anr.mm"
include "sylibrd.mm"
include "necon1bd.mm"
include "mpd.mm"
include "simpr.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "fzfid.mm"
include "fsumss.mm"
include "eqtr4d.mm"
include "mpteq2dva.mm"

theorem coeidlem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let cX: class X
  assume dgrub.1: |- A = ( coeff ` F )
  assume dgrub.2: |- N = ( deg ` F )
  assume coeid.3: |- ( ph -> F e. ( Poly ` S ) )
  assume coeid.4: |- ( ph -> M e. NN0 )
  assume coeid.5: |- ( ph -> B e. ( ( S u. { 0 } ) ^m NN0 ) )
  assume coeid.6: |- ( ph -> ( B " ( ZZ>= ` ( M + 1 ) ) ) = { 0 } )
  assume coeid.7: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... M ) ( ( B ` k ) x. ( z ^ k ) ) ) )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint F k
  disjoint k ph
  disjoint ph z
  disjoint S k
  disjoint S z
  disjoint B k
  disjoint B z
  disjoint M k
  disjoint M z
  disjoint N k
  disjoint N z
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint F a
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint a m
  disjoint S a
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint M y
  disjoint N a
  disjoint N n
  disjoint X k
  disjoint X z
  assert |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( z ^ k ) ) ) )

  proof
    wph
    cF
    vz
    cc
    cc0
    cM
    cfz
    co
    #
    vk
    cv
    #
    cB
    cfv
    #
    vz
    cv
    #
    @1
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    @1
    cA
    cfv
    #
    @4
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    coeid.7
    wph
    vz
    cc
    @6
    @10
    wph
    @3
    cc
    wcel
    #
    wa
    #
    @6
    @0
    @9
    vk
    csu
    #
    @10
    @12
    cB
    cA
    wceq
    #
    @6
    @13
    wceq
    wph
    @14
    @11
    wph
    cA
    cF
    ccoe
    cfv
    cB
    dgrub.1
    wph
    vz
    cB
    cS
    vk
    cF
    cM
    coeid.3
    coeid.4
    wph
    cn0
    cS
    cc0
    csn
    #
    cun
    #
    cc
    cB
    wph
    cB
    @16
    cn0
    cmap
    co
    wcel
    #
    cn0
    @16
    cB
    wf
    #
    coeid.5
    wph
    @16
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    @17
    @18
    wb
    wph
    @16
    cc
    wss
    cc
    cvv
    wcel
    @19
    wph
    cS
    @15
    cc
    wph
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cS
    cc
    wss
    coeid.3
    cS
    cF
    plybss
    syl
    wph
    cc0
    cc
    wph
    0cnd
    snssd
    unssd
    #
    cnex
    @16
    cc
    cvv
    ssexg
    sylancl
    nn0ex
    @16
    cn0
    cB
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    @22
    fssd
    coeid.6
    coeid.7
    coeeq
    syl5req
    adantr
    #
    @14
    @0
    @5
    @9
    vk
    @14
    @2
    @8
    @4
    cmul
    @1
    cB
    cA
    fveq1
    oveq1d
    sumeq2sdv
    syl
    @12
    @7
    @0
    @9
    vk
    @12
    cM
    cN
    cuz
    cfv
    wcel
    #
    @7
    @0
    wss
    @12
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    cN
    cM
    cle
    wbr
    #
    @24
    @12
    cN
    @12
    @21
    cN
    cn0
    wcel
    wph
    @21
    @11
    coeid.3
    adantr
    #
    @21
    cN
    cF
    cdgr
    cfv
    cn0
    dgrub.2
    cS
    cF
    dgrcl
    syl5eqel
    syl
    nn0zd
    #
    @12
    cM
    wph
    cM
    cn0
    wcel
    #
    @11
    coeid.4
    adantr
    #
    nn0zd
    @12
    @21
    @29
    cA
    cM
    c1
    caddc
    co
    cuz
    cfv
    #
    cima
    #
    @15
    wceq
    @26
    @27
    @30
    @12
    cB
    @31
    cima
    #
    @32
    @15
    @12
    cB
    cA
    @31
    @23
    imaeq1d
    wph
    @33
    @15
    wceq
    @11
    coeid.6
    adantr
    eqtr3d
    cA
    cS
    cF
    cM
    cN
    dgrub.1
    dgrub.2
    dgrlb
    syl3anc
    cN
    cM
    eluz2
    syl3anbrc
    cN
    cc0
    cM
    fzss2
    syl
    @1
    @7
    wcel
    #
    @12
    @1
    cn0
    wcel
    #
    @9
    cc
    wcel
    @1
    cN
    elfznn0
    @12
    @35
    wa
    @8
    @4
    @12
    cn0
    cc
    @1
    cA
    wph
    cn0
    cc
    cA
    wf
    #
    @11
    wph
    cF
    cc
    cply
    cfv
    #
    wcel
    @36
    wph
    @20
    @37
    cF
    cS
    plyssc
    coeid.3
    sseldi
    cA
    cc
    cF
    dgrub.1
    coef3
    syl
    adantr
    ffvelrnda
    @11
    @35
    @4
    cc
    wcel
    #
    wph
    @3
    @1
    expcl
    #
    adantll
    mulcld
    sylan2
    @12
    @1
    @0
    @7
    cdif
    wcel
    #
    wa
    #
    @9
    cc0
    @4
    cmul
    co
    cc0
    @41
    @8
    cc0
    @4
    cmul
    @41
    @34
    wn
    #
    @8
    cc0
    wceq
    @40
    @42
    @12
    @1
    @0
    @7
    eldifn
    adantl
    @41
    @34
    @8
    cc0
    @41
    @8
    cc0
    wne
    #
    @1
    cN
    cle
    wbr
    #
    @34
    @12
    @21
    @35
    @43
    @44
    wi
    @40
    @27
    @40
    @1
    @0
    wcel
    #
    @35
    @1
    @0
    @7
    eldifi
    #
    @1
    cM
    elfznn0
    syl
    #
    @21
    @35
    @43
    @44
    cA
    cS
    cF
    @1
    cN
    dgrub.1
    dgrub.2
    dgrub
    3expia
    syl2an
    @40
    @1
    cc0
    cuz
    cfv
    wcel
    #
    @25
    @34
    @44
    wb
    @12
    @40
    @45
    @48
    @46
    @1
    cc0
    cM
    elfzuz
    syl
    @28
    @1
    cc0
    cN
    elfz5
    syl2anr
    sylibrd
    necon1bd
    mpd
    oveq1d
    @41
    @4
    @12
    @11
    @35
    @38
    @40
    wph
    @11
    simpr
    @47
    @39
    syl2an
    mul02d
    eqtrd
    @12
    cc0
    cM
    fzfid
    fsumss
    eqtr4d
    mpteq2dva
    eqtrd
end

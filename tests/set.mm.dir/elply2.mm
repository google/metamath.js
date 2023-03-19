include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "cfz.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wa.mm"
include "cun.mm"
include "cn0.mm"
include "cmap.mm"
include "wrex.mm"
include "elply.mm"
include "cif.mm"
include "wf.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "simpll.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "snex.mm"
include "unexg.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpbid.mm"
include "ffvelrnda.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "ifcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "mpbird.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "ad2antll.mm"
include "iffalse.mm"
include "eqeq2d.mm"
include "syl5ibcom.mm"
include "necon1ad.mm"
include "elfzle2.mm"
include "syl6.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "simplr.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "fssd.mm"
include "plyco0.mm"
include "syl2anc.mm"
include "eqidd.mm"
include "imaeq1.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "elfznn0.mm"
include "syl.mm"
include "iftrue.mm"
include "eqtrd.mm"
include "sylan9eq.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "mpteq2dv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "reximdva.mm"
include "imdistani.mm"
include "sylbi.mm"
include "reximi.mm"
include "anim2i.mm"
include "sylibr.mm"
include "impbii.mm"

theorem elply2
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let va: setvar a
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let cT: class T

  disjoint a k
  disjoint a n
  disjoint a z
  disjoint k n
  disjoint k z
  disjoint n z
  disjoint S a
  disjoint S k
  disjoint S n
  disjoint S z
  disjoint F a
  disjoint F n
  disjoint A a
  disjoint A k
  disjoint A n
  disjoint A z
  disjoint N a
  disjoint N k
  disjoint N n
  disjoint N z
  disjoint a f
  disjoint a x
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f z
  disjoint S f
  disjoint k x
  disjoint n x
  disjoint x z
  disjoint S x
  disjoint T a
  disjoint T f
  disjoint T k
  disjoint T n
  disjoint T z
  disjoint F f
  assert |- ( F e. ( Poly ` S ) <-> ( S C_ CC /\ E. n e. NN0 E. a e. ( ( S u. { 0 } ) ^m NN0 ) ( ( a " ( ZZ>= ` ( n + 1 ) ) ) = { 0 } /\ F = ( z e. CC |-> sum_ k e. ( 0 ... n ) ( ( a ` k ) x. ( z ^ k ) ) ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cS
    cc
    wss
    #
    va
    cv
    #
    vn
    cv
    #
    c1
    caddc
    co
    cuz
    cfv
    #
    cima
    #
    cc0
    csn
    #
    wceq
    #
    cF
    vz
    cc
    cc0
    @3
    cfz
    co
    #
    vk
    cv
    #
    @2
    cfv
    #
    vz
    cv
    @9
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
    #
    wceq
    #
    wa
    #
    va
    cS
    @6
    cun
    #
    cn0
    cmap
    co
    #
    wrex
    #
    vn
    cn0
    wrex
    #
    wa
    #
    @0
    @1
    cF
    vz
    cc
    @8
    @9
    vf
    cv
    #
    cfv
    #
    @11
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    wceq
    #
    vf
    @18
    wrex
    #
    vn
    cn0
    wrex
    #
    wa
    @21
    vz
    cS
    vk
    vn
    cF
    vf
    elply
    @1
    @29
    @20
    @1
    @28
    @19
    vn
    cn0
    @1
    @3
    cn0
    wcel
    #
    wa
    #
    @27
    @19
    vf
    @18
    @31
    @22
    @18
    wcel
    #
    wa
    #
    @19
    @27
    @7
    @26
    @14
    wceq
    #
    wa
    #
    va
    @18
    wrex
    #
    @33
    vx
    cn0
    vx
    cv
    #
    @8
    wcel
    #
    @37
    @22
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    @18
    wcel
    #
    @41
    @4
    cima
    #
    @6
    wceq
    #
    @26
    @26
    wceq
    #
    @36
    @33
    @42
    cn0
    @17
    @41
    wf
    #
    @33
    vx
    cn0
    @40
    @17
    @41
    @33
    @37
    cn0
    wcel
    wa
    @39
    @17
    wcel
    cc0
    @17
    wcel
    #
    @40
    @17
    wcel
    @33
    cn0
    @17
    @37
    @22
    @33
    @32
    cn0
    @17
    @22
    wf
    #
    @31
    @32
    simpr
    @33
    @17
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    @32
    @48
    wb
    @33
    cS
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @49
    @33
    @1
    cc
    cvv
    wcel
    @51
    @1
    @30
    @32
    simpll
    #
    cnex
    cS
    cc
    cvv
    ssexg
    sylancl
    cc0
    snex
    cS
    @6
    cvv
    cvv
    unexg
    sylancl
    #
    nn0ex
    @17
    cn0
    @22
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    ffvelrnda
    @47
    @6
    @17
    wss
    @6
    cS
    ssun2
    cc0
    @17
    c0ex
    snss
    mpbir
    @38
    @39
    cc0
    @17
    ifcl
    sylancl
    @41
    eqid
    #
    fmptd
    #
    @33
    @49
    @50
    @42
    @46
    wb
    @53
    nn0ex
    @17
    cn0
    @41
    cvv
    cvv
    elmapg
    sylancl
    mpbird
    @33
    @44
    @9
    @41
    cfv
    #
    cc0
    wne
    #
    @9
    @3
    cle
    wbr
    #
    wi
    #
    vk
    cn0
    wral
    #
    @33
    @59
    vk
    cn0
    @31
    @32
    @9
    cn0
    wcel
    #
    @59
    @31
    @32
    @61
    wa
    wa
    #
    @57
    @9
    @8
    wcel
    #
    @58
    @62
    @63
    @56
    cc0
    @62
    @56
    @63
    @23
    cc0
    cif
    #
    wceq
    #
    @63
    wn
    #
    @56
    cc0
    wceq
    @61
    @65
    @31
    @32
    vx
    @9
    @40
    @64
    cn0
    @41
    @37
    @9
    wceq
    @38
    @63
    @39
    @23
    cc0
    @37
    @9
    @8
    eleq1
    @37
    @9
    @22
    fveq2
    ifbieq1d
    @54
    @63
    @23
    cc0
    @9
    @22
    fvex
    c0ex
    ifex
    fvmpt
    #
    ad2antll
    @66
    @64
    cc0
    @56
    @63
    @23
    cc0
    iffalse
    eqeq2d
    syl5ibcom
    necon1ad
    @9
    cc0
    @3
    elfzle2
    syl6
    anassrs
    ralrimiva
    @33
    @30
    cn0
    cc
    @41
    wf
    @44
    @60
    wb
    @1
    @30
    @32
    simplr
    @33
    cn0
    @17
    cc
    @41
    @55
    @33
    cS
    @6
    cc
    @52
    @33
    cc0
    cc
    @33
    0cnd
    snssd
    unssd
    fssd
    @41
    vk
    @3
    plyco0
    syl2anc
    mpbird
    @33
    @26
    eqidd
    @35
    @44
    @45
    wa
    va
    @41
    @18
    @2
    @41
    wceq
    #
    @7
    @44
    @34
    @45
    @68
    @5
    @43
    @6
    @2
    @41
    @4
    imaeq1
    eqeq1d
    @68
    @14
    @26
    @26
    @68
    vz
    cc
    @13
    @25
    @68
    @8
    @12
    @24
    vk
    @68
    @63
    wa
    @10
    @23
    @11
    cmul
    @68
    @63
    @10
    @56
    @23
    @9
    @2
    @41
    fveq1
    @63
    @56
    @64
    @23
    @63
    @61
    @65
    @9
    @3
    elfznn0
    @67
    syl
    @63
    @23
    cc0
    iftrue
    eqtrd
    sylan9eq
    oveq1d
    sumeq2dv
    mpteq2dv
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @27
    @16
    @35
    va
    @18
    @27
    @15
    @34
    @7
    cF
    @26
    @14
    eqeq1
    anbi2d
    rexbidv
    syl5ibrcom
    rexlimdva
    reximdva
    imdistani
    sylbi
    @21
    @1
    @15
    va
    @18
    wrex
    #
    vn
    cn0
    wrex
    #
    wa
    @0
    @20
    @70
    @1
    @19
    @69
    vn
    cn0
    @16
    @15
    va
    @18
    @7
    @15
    simpr
    reximi
    reximi
    anim2i
    vz
    cS
    vk
    vn
    cF
    va
    elply
    sylibr
    impbii
end

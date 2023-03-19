include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "ccj.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "ccom.mm"
include "cjcl.mm"
include "adantl.mm"
include "wf.mm"
include "cjf.mm"
include "a1i.mm"
include "feqmptd.mm"
include "wa.mm"
include "fzfid.mm"
include "cn0.mm"
include "coef3.mm"
include "adantr.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "expcl.mm"
include "sylan2.mm"
include "adantll.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "coeid.mm"
include "fveq2.mm"
include "fmptco.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "fsumcj.mm"
include "cjmuld.mm"
include "fvco3.mm"
include "cjexp.mm"
include "cjcj.mm"
include "ad2antlr.mm"
include "oveq1d.mm"
include "eqtr2d.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "sumeq2dv.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"

theorem plycjlem
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cN: class N
  let vx: setvar x
  let wph: wff ph
  assume plycj.1: |- N = ( deg ` F )
  assume plycj.2: |- G = ( ( * o. F ) o. * )
  assume plycjlem.3: |- A = ( coeff ` F )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint F k
  disjoint F z
  disjoint N k
  disjoint N z
  disjoint S k
  disjoint S z
  disjoint k x
  disjoint x z
  disjoint A x
  disjoint F x
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint S x
  assert |- ( F e. ( Poly ` S ) -> G = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( ( * o. A ) ` k ) x. ( z ^ k ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cG
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    vz
    cv
    #
    ccj
    cfv
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    ccj
    cfv
    #
    cmpt
    #
    vz
    cc
    @1
    @2
    ccj
    cA
    ccom
    cfv
    #
    @4
    @2
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
    @0
    cG
    ccj
    cF
    ccom
    #
    ccj
    ccom
    @10
    plycj.2
    @0
    vz
    vx
    cc
    cc
    @5
    @1
    @3
    vx
    cv
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    ccj
    cfv
    #
    @9
    ccj
    @15
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @0
    @4
    cjcl
    adantl
    #
    @0
    vz
    cc
    cc
    ccj
    cc
    cc
    ccj
    wf
    @0
    cjf
    a1i
    feqmptd
    #
    @0
    vx
    vz
    cc
    cc
    @19
    @5
    @20
    cF
    ccj
    @0
    @16
    cc
    wcel
    #
    wa
    #
    @1
    @18
    vk
    @26
    cc0
    cN
    fzfid
    @26
    @2
    @1
    wcel
    #
    wa
    @3
    @17
    @26
    cn0
    cc
    cA
    wf
    #
    @2
    cn0
    wcel
    #
    @3
    cc
    wcel
    #
    @27
    @0
    @28
    @25
    cA
    cS
    cF
    plycjlem.3
    coef3
    #
    adantr
    @2
    cN
    elfznn0
    #
    cn0
    cc
    @2
    cA
    ffvelrn
    #
    syl2an
    @25
    @27
    @17
    cc
    wcel
    #
    @0
    @27
    @25
    @29
    @34
    @32
    @16
    @2
    expcl
    sylan2
    adantll
    mulcld
    fsumcl
    vx
    cA
    cS
    vk
    cF
    cN
    plycjlem.3
    plycj.1
    coeid
    @24
    @4
    @19
    ccj
    fveq2
    fmptco
    @16
    @5
    wceq
    #
    @19
    @8
    ccj
    @35
    @1
    @18
    @7
    vk
    @35
    @17
    @6
    @3
    cmul
    @16
    @5
    @2
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    fveq2d
    fmptco
    syl5eq
    @0
    vz
    cc
    @9
    @14
    @0
    @21
    wa
    #
    @9
    @1
    @7
    ccj
    cfv
    #
    vk
    csu
    @14
    @36
    @1
    @7
    vk
    @36
    cc0
    cN
    fzfid
    @36
    @27
    wa
    #
    @3
    @6
    @36
    @28
    @29
    @30
    @27
    @0
    @28
    @21
    @31
    adantr
    #
    @32
    @33
    syl2an
    #
    @36
    @22
    @29
    @6
    cc
    wcel
    @27
    @23
    @32
    @5
    @2
    expcl
    syl2an
    #
    mulcld
    fsumcj
    @36
    @1
    @37
    @13
    vk
    @38
    @37
    @3
    ccj
    cfv
    #
    @6
    ccj
    cfv
    #
    cmul
    co
    @13
    @38
    @3
    @6
    @40
    @41
    cjmuld
    @38
    @11
    @42
    @12
    @43
    cmul
    @36
    @28
    @29
    @11
    @42
    wceq
    @27
    @39
    @32
    cn0
    cc
    @2
    ccj
    cA
    fvco3
    syl2an
    @38
    @43
    @5
    ccj
    cfv
    #
    @2
    cexp
    co
    #
    @12
    @36
    @22
    @29
    @43
    @45
    wceq
    @27
    @23
    @32
    @5
    @2
    cjexp
    syl2an
    @38
    @44
    @4
    @2
    cexp
    @21
    @44
    @4
    wceq
    @0
    @27
    @4
    cjcj
    ad2antlr
    oveq1d
    eqtr2d
    oveq12d
    eqtr4d
    sumeq2dv
    eqtrd
    mpteq2dva
    eqtrd
end

include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "wa.mm"
include "wral.mm"
include "clt.mm"
include "cmin.mm"
include "co.mm"
include "w3a.mm"
include "wrex.mm"
include "cmpt.mm"
include "cr.mm"
include "1re.mm"
include "stoweidlem4.mm"
include "mpan2.mm"
include "syl5eqel.mm"
include "0le1.mm"
include "wceq.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "syl5breqr.mm"
include "1le1.mm"
include "syl6eqbr.mm"
include "jca.mm"
include "ex.mm"
include "ralrimi.mm"
include "c0.mm"
include "nfcv.mm"
include "nfeq.mm"
include "rzalf.mm"
include "syl.mm"
include "1red.mm"
include "ltsubrpd.mm"
include "adantr.mm"
include "ccld.mm"
include "wss.mm"
include "cldss.mm"
include "sselda.mm"
include "breqtrrd.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "fveq1.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbid.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"

theorem stoweidlem18
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cT: class T
  let cE: class E
  let cF: class F
  let cJ: class J
  let va: setvar a
  let vk: setvar k
  assume stoweidlem18.1: |- F/_ t D
  assume stoweidlem18.2: |- F/ t ph
  assume stoweidlem18.3: |- F = ( t e. T |-> 1 )
  assume stoweidlem18.4: |- T = U. J
  assume stoweidlem18.5: |- ( ( ph /\ a e. RR ) -> ( t e. T |-> a ) e. A )
  assume stoweidlem18.6: |- ( ph -> B e. ( Clsd ` J ) )
  assume stoweidlem18.7: |- ( ph -> E e. RR+ )
  assume stoweidlem18.8: |- ( ph -> D = (/) )

  disjoint a t
  disjoint T a
  disjoint T t
  disjoint A a
  disjoint a ph
  disjoint t x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint E x
  disjoint F x
  disjoint T x
  disjoint k x
  assert |- ( ph -> E. x e. A ( A. t e. T ( 0 <_ ( x ` t ) /\ ( x ` t ) <_ 1 ) /\ A. t e. D ( x ` t ) < E /\ A. t e. B ( 1 - E ) < ( x ` t ) ) )

  proof
    wph
    cF
    cA
    wcel
    cc0
    vt
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    @1
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @1
    cE
    clt
    wbr
    #
    vt
    cD
    wral
    #
    c1
    cE
    cmin
    co
    #
    @1
    clt
    wbr
    #
    vt
    cB
    wral
    #
    cc0
    @0
    vx
    cv
    #
    cfv
    #
    cle
    wbr
    #
    @12
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @12
    cE
    clt
    wbr
    #
    vt
    cD
    wral
    #
    @8
    @12
    clt
    wbr
    #
    vt
    cB
    wral
    #
    w3a
    #
    vx
    cA
    wrex
    wph
    cF
    vt
    cT
    c1
    cmpt
    #
    cA
    stoweidlem18.3
    wph
    c1
    cr
    wcel
    #
    @22
    cA
    wcel
    1re
    wph
    va
    vt
    cA
    c1
    cT
    stoweidlem18.5
    stoweidlem4
    mpan2
    syl5eqel
    wph
    @4
    vt
    cT
    stoweidlem18.2
    wph
    @0
    cT
    wcel
    #
    @4
    wph
    @24
    wa
    #
    @2
    @3
    @25
    cc0
    c1
    @1
    cle
    0le1
    @25
    @24
    @23
    @1
    c1
    wceq
    #
    wph
    @24
    simpr
    1re
    vt
    cT
    c1
    cr
    cF
    stoweidlem18.3
    fvmpt2
    #
    sylancl
    #
    syl5breqr
    @25
    @1
    c1
    c1
    cle
    @28
    1le1
    syl6eqbr
    jca
    ex
    ralrimi
    wph
    cD
    c0
    wceq
    @7
    stoweidlem18.8
    @6
    vt
    cD
    vt
    cD
    c0
    stoweidlem18.1
    vt
    c0
    nfcv
    nfeq
    rzalf
    syl
    wph
    @9
    vt
    cB
    stoweidlem18.2
    wph
    @0
    cB
    wcel
    #
    @9
    wph
    @29
    wa
    #
    @8
    c1
    @1
    clt
    wph
    @8
    c1
    clt
    wbr
    @29
    wph
    c1
    cE
    wph
    1red
    stoweidlem18.7
    ltsubrpd
    adantr
    @30
    @24
    @23
    @26
    wph
    cB
    cT
    @0
    wph
    cB
    cJ
    ccld
    cfv
    wcel
    cB
    cT
    wss
    stoweidlem18.6
    cB
    cJ
    cT
    stoweidlem18.4
    cldss
    syl
    sselda
    1re
    @27
    sylancl
    breqtrrd
    ex
    ralrimi
    @21
    @5
    @7
    @10
    w3a
    vx
    cF
    cA
    @11
    cF
    wceq
    #
    @16
    @5
    @18
    @7
    @20
    @10
    @31
    @15
    @4
    vt
    cT
    vt
    @11
    cF
    vt
    @11
    nfcv
    vt
    cF
    @22
    stoweidlem18.3
    vt
    cT
    c1
    nfmpt1
    nfcxfr
    nfeq
    #
    @31
    @13
    @2
    @14
    @3
    @31
    @12
    @1
    cc0
    cle
    @0
    @11
    cF
    fveq1
    #
    breq2d
    @31
    @12
    @1
    c1
    cle
    @33
    breq1d
    anbi12d
    ralbid
    @31
    @17
    @6
    vt
    cD
    @32
    @31
    @12
    @1
    cE
    clt
    @33
    breq1d
    ralbid
    @31
    @19
    @9
    vt
    cB
    @32
    @31
    @12
    @1
    @8
    clt
    @33
    breq2d
    ralbid
    3anbi123d
    rspcev
    syl13anc
end

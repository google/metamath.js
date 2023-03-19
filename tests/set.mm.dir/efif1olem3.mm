include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "csqrt.mm"
include "cfv.mm"
include "cim.mm"
include "cr.mm"
include "c1.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "cc.mm"
include "cabs.mm"
include "wceq.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "absf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "sylib.mm"
include "simpld.mm"
include "sqrtcld.mm"
include "imcld.mm"
include "absimle.mm"
include "syl.mm"
include "c2.mm"
include "cexp.mm"
include "sqsqrtd.mm"
include "fveq2d.mm"
include "cn0.mm"
include "2nn0.mm"
include "absexp.mm"
include "sylancl.mm"
include "simprd.mm"
include "3eqtr3d.mm"
include "sq1.mm"
include "syl6eqr.mm"
include "cc0.mm"
include "abscld.mm"
include "absge0d.mm"
include "1re.mm"
include "0le1.mm"
include "sq11.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "breqtrd.mm"
include "absle.mm"
include "neg1rr.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"

theorem efif1olem3
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cF: class F
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cS: class S
  assume efif1o.1: |- F = ( w e. D |-> ( exp ` ( _i x. w ) ) )
  assume efif1o.2: |- C = ( `' abs " { 1 } )

  disjoint w x
  disjoint C w
  disjoint C x
  disjoint F x
  disjoint ph w
  disjoint ph x
  disjoint D w
  disjoint D x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C y
  disjoint F y
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint D y
  disjoint D z
  assert |- ( ( ph /\ x e. C ) -> ( Im ` ( sqrt ` x ) ) e. ( -u 1 [,] 1 ) )

  proof
    wph
    vx
    cv
    #
    cC
    wcel
    #
    wa
    #
    @0
    csqrt
    cfv
    #
    cim
    cfv
    #
    cr
    wcel
    #
    c1
    cneg
    #
    @4
    cle
    wbr
    #
    @4
    c1
    cle
    wbr
    #
    @4
    @6
    c1
    cicc
    co
    wcel
    @2
    @3
    @2
    @0
    @2
    @0
    cc
    wcel
    #
    @0
    cabs
    cfv
    #
    c1
    wceq
    #
    @2
    @0
    cabs
    ccnv
    c1
    csn
    cima
    #
    wcel
    #
    @9
    @11
    wa
    #
    @2
    @0
    cC
    @12
    wph
    @1
    simpr
    efif1o.2
    syl6eleq
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @13
    @14
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    c1
    @0
    cabs
    fniniseg
    mp2b
    sylib
    #
    simpld
    #
    sqrtcld
    #
    imcld
    #
    @2
    @7
    @8
    @2
    @4
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @7
    @8
    wa
    #
    @2
    @19
    @3
    cabs
    cfv
    #
    c1
    cle
    @2
    @3
    cc
    wcel
    #
    @19
    @22
    cle
    wbr
    @17
    @3
    absimle
    syl
    @2
    @22
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @22
    c1
    wceq
    #
    @2
    @24
    c1
    @25
    @2
    @3
    c2
    cexp
    co
    #
    cabs
    cfv
    #
    @10
    @24
    c1
    @2
    @28
    @0
    cabs
    @2
    @0
    @16
    sqsqrtd
    fveq2d
    @2
    @23
    c2
    cn0
    wcel
    @29
    @24
    wceq
    @17
    2nn0
    @3
    c2
    absexp
    sylancl
    @2
    @9
    @11
    @15
    simprd
    3eqtr3d
    sq1
    syl6eqr
    @2
    @22
    cr
    wcel
    #
    cc0
    @22
    cle
    wbr
    #
    @26
    @27
    wb
    #
    @2
    @3
    @17
    abscld
    @2
    @3
    @17
    absge0d
    @30
    @31
    wa
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    @32
    1re
    0le1
    @22
    c1
    sq11
    mpanr12
    syl2anc
    mpbid
    breqtrd
    @2
    @5
    @33
    @20
    @21
    wb
    @18
    1re
    @4
    c1
    absle
    sylancl
    mpbid
    #
    simpld
    @2
    @7
    @8
    @34
    simprd
    @6
    c1
    @4
    neg1rr
    1re
    elicc2i
    syl3anbrc
end

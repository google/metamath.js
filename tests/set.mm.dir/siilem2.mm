include "cc.mm"
include "wcel.mm"
include "co.mm"
include "cmul.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "csqrt.mm"
include "wi.mm"
include "cif.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "breq2d.mm"
include "3anbi123d.mm"
include "0cn.mm"
include "cnv.mm"
include "phnvi.mm"
include "dipcl.mm"
include "mp3an.mm"
include "mul02i.mm"
include "0re.mm"
include "eqeltri.mm"
include "0le0.mm"
include "breqtrri.mm"
include "3pm3.2i.mm"
include "elimhyp.mm"
include "simp1i.mm"
include "simp2i.mm"
include "simp3i.mm"
include "siilem1.mm"
include "dedth.mm"

theorem siilem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cM: class M
  let cN: class N
  let cX: class X
  assume siii.1: |- X = ( BaseSet ` U )
  assume siii.6: |- N = ( normCV ` U )
  assume siii.7: |- P = ( .iOLD ` U )
  assume siii.9: |- U e. CPreHilOLD
  assume siii.a: |- A e. X
  assume siii.b: |- B e. X
  assume siii2.3: |- M = ( -v ` U )
  assume siii2.4: |- S = ( .sOLD ` U )


  assert |- ( ( C e. CC /\ ( C x. ( A P B ) ) e. RR /\ 0 <_ ( C x. ( A P B ) ) ) -> ( ( B P A ) = ( C x. ( ( N ` B ) ^ 2 ) ) -> ( sqrt ` ( ( A P B ) x. ( C x. ( ( N ` B ) ^ 2 ) ) ) ) <_ ( ( N ` A ) x. ( N ` B ) ) ) )

  proof
    cC
    cc
    wcel
    #
    cC
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    w3a
    #
    cB
    cA
    cP
    co
    #
    cC
    cB
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    wceq
    #
    @1
    @9
    cmul
    co
    #
    csqrt
    cfv
    #
    cA
    cN
    cfv
    @7
    cmul
    co
    #
    cle
    wbr
    #
    wi
    @6
    @5
    cC
    cc0
    cif
    #
    @8
    cmul
    co
    #
    wceq
    #
    @1
    @16
    cmul
    co
    #
    csqrt
    cfv
    #
    @13
    cle
    wbr
    #
    wi
    cC
    cc0
    cC
    @15
    wceq
    #
    @10
    @17
    @14
    @20
    @21
    @9
    @16
    @6
    cC
    @15
    @8
    cmul
    oveq1
    #
    eqeq2d
    @21
    @12
    @19
    @13
    cle
    @21
    @11
    @18
    csqrt
    @21
    @9
    @16
    @1
    cmul
    @22
    oveq2d
    fveq2d
    breq1d
    imbi12d
    cA
    cB
    @15
    cP
    cS
    cU
    cM
    cN
    cX
    siii.1
    siii.6
    siii.7
    siii.9
    siii.a
    siii.b
    siii2.3
    siii2.4
    @15
    cc
    wcel
    #
    @15
    @1
    cmul
    co
    #
    cr
    wcel
    #
    cc0
    @24
    cle
    wbr
    #
    @5
    @23
    @25
    @26
    w3a
    cc0
    cc
    wcel
    #
    cc0
    @1
    cmul
    co
    #
    cr
    wcel
    #
    cc0
    @28
    cle
    wbr
    #
    w3a
    cC
    cc0
    @21
    @0
    @23
    @3
    @25
    @4
    @26
    cC
    @15
    cc
    eleq1
    @21
    @2
    @24
    cr
    cC
    @15
    @1
    cmul
    oveq1
    #
    eleq1d
    @21
    @2
    @24
    cc0
    cle
    @31
    breq2d
    3anbi123d
    cc0
    @15
    wceq
    #
    @27
    @23
    @29
    @25
    @30
    @26
    cc0
    @15
    cc
    eleq1
    @32
    @28
    @24
    cr
    cc0
    @15
    @1
    cmul
    oveq1
    #
    eleq1d
    @32
    @28
    @24
    cc0
    cle
    @33
    breq2d
    3anbi123d
    @27
    @29
    @30
    0cn
    @28
    cc0
    cr
    @1
    cU
    cnv
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    @1
    cc
    wcel
    cU
    siii.9
    phnvi
    siii.a
    siii.b
    cA
    cB
    cP
    cU
    cX
    siii.1
    siii.7
    dipcl
    mp3an
    mul02i
    #
    0re
    eqeltri
    cc0
    cc0
    @28
    cle
    0le0
    @34
    breqtrri
    3pm3.2i
    elimhyp
    #
    simp1i
    @23
    @25
    @26
    @35
    simp2i
    @23
    @25
    @26
    @35
    simp3i
    siilem1
    dedth
end

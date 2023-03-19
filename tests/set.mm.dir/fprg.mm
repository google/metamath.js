include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cop.mm"
include "wf.mm"
include "cvv.mm"
include "wi.mm"
include "elex.mm"
include "anim12i.mm"
include "c0.mm"
include "cif.mm"
include "wceq.mm"
include "neeq1.mm"
include "opeq1.mm"
include "preq1d.mm"
include "preq1.mm"
include "feq12d.mm"
include "imbi12d.mm"
include "neeq2.mm"
include "preq2d.mm"
include "preq2.mm"
include "opeq2.mm"
include "eqidd.mm"
include "feq123d.mm"
include "imbi2d.mm"
include "0ex.mm"
include "elimel.mm"
include "fpr.mm"
include "dedth4h.mm"
include "syl2an.mm"
include "3impia.mm"

theorem fprg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H


  assert |- ( ( ( A e. E /\ B e. F ) /\ ( C e. G /\ D e. H ) /\ A =/= B ) -> { <. A , C >. , <. B , D >. } : { A , B } --> { C , D } )

  proof
    cA
    cE
    wcel
    #
    cB
    cF
    wcel
    #
    wa
    #
    cC
    cG
    wcel
    #
    cD
    cH
    wcel
    #
    wa
    #
    cA
    cB
    wne
    #
    cA
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    cA
    cC
    cop
    #
    cB
    cD
    cop
    #
    cpr
    #
    wf
    #
    @2
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    cC
    cvv
    wcel
    #
    cD
    cvv
    wcel
    #
    wa
    @6
    @12
    wi
    #
    @5
    @0
    @13
    @1
    @14
    cA
    cE
    elex
    cB
    cF
    elex
    anim12i
    @3
    @15
    @4
    @16
    cC
    cG
    elex
    cD
    cH
    elex
    anim12i
    @13
    @14
    @15
    @16
    @17
    @13
    cA
    c0
    cif
    #
    cB
    wne
    #
    @18
    cB
    cpr
    #
    @8
    @18
    cC
    cop
    #
    @10
    cpr
    #
    wf
    #
    wi
    @18
    @14
    cB
    c0
    cif
    #
    wne
    #
    @18
    @24
    cpr
    #
    @8
    @21
    @24
    cD
    cop
    #
    cpr
    #
    wf
    #
    wi
    @25
    @26
    @15
    cC
    c0
    cif
    #
    cD
    cpr
    #
    @18
    @30
    cop
    #
    @27
    cpr
    #
    wf
    #
    wi
    @25
    @26
    @30
    @16
    cD
    c0
    cif
    #
    cpr
    #
    @32
    @24
    @35
    cop
    #
    cpr
    #
    wf
    #
    wi
    cA
    cB
    cC
    cD
    c0
    c0
    c0
    c0
    cA
    @18
    wceq
    #
    @6
    @19
    @12
    @23
    cA
    @18
    cB
    neeq1
    @40
    @7
    @20
    @8
    @11
    @22
    @40
    @9
    @21
    @10
    cA
    @18
    cC
    opeq1
    preq1d
    cA
    @18
    cB
    preq1
    feq12d
    imbi12d
    cB
    @24
    wceq
    #
    @19
    @25
    @23
    @29
    cB
    @24
    @18
    neeq2
    @41
    @20
    @26
    @8
    @22
    @28
    @41
    @10
    @27
    @21
    cB
    @24
    cD
    opeq1
    preq2d
    cB
    @24
    @18
    preq2
    feq12d
    imbi12d
    cC
    @30
    wceq
    #
    @29
    @34
    @25
    @42
    @26
    @26
    @8
    @31
    @28
    @33
    @42
    @21
    @32
    @27
    cC
    @30
    @18
    opeq2
    preq1d
    @42
    @26
    eqidd
    cC
    @30
    cD
    preq1
    feq123d
    imbi2d
    cD
    @35
    wceq
    #
    @34
    @39
    @25
    @43
    @26
    @26
    @31
    @36
    @33
    @38
    @43
    @27
    @37
    @32
    cD
    @35
    @24
    opeq2
    preq2d
    @43
    @26
    eqidd
    cD
    @35
    @30
    preq2
    feq123d
    imbi2d
    @18
    @24
    @30
    @35
    cA
    c0
    cvv
    0ex
    elimel
    cB
    c0
    cvv
    0ex
    elimel
    cC
    c0
    cvv
    0ex
    elimel
    cD
    c0
    cvv
    0ex
    elimel
    fpr
    dedth4h
    syl2an
    3impia
end

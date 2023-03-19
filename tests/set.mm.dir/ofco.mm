include "cof.mm"
include "co.mm"
include "ccom.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fmptco.mm"
include "wfn.mm"
include "wf.mm"
include "wss.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstr3i.mm"
include "fss.mm"
include "sylancl.mm"
include "fnfco.mm"
include "syl2anc.mm"
include "inss2.mm"
include "inidm.mm"
include "ffn.mm"
include "syl.mm"
include "fvco2.mm"
include "sylan.mm"
include "eqtr4d.mm"

theorem ofco
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let vy: setvar y
  let vx: setvar x
  assume ofco.1: |- ( ph -> F Fn A )
  assume ofco.2: |- ( ph -> G Fn B )
  assume ofco.3: |- ( ph -> H : D --> C )
  assume ofco.4: |- ( ph -> A e. V )
  assume ofco.5: |- ( ph -> B e. W )
  assume ofco.6: |- ( ph -> D e. X )
  assume ofco.7: |- ( A i^i B ) = C


  assert |- ( ph -> ( ( F oF R G ) o. H ) = ( ( F o. H ) oF R ( G o. H ) ) )

  proof
    wph
    cF
    cG
    cR
    cof
    #
    co
    #
    cH
    ccom
    vx
    cD
    vx
    cv
    #
    cH
    cfv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    cF
    cH
    ccom
    #
    cG
    cH
    ccom
    #
    @0
    co
    wph
    vx
    vy
    cD
    cC
    @3
    vy
    cv
    #
    cF
    cfv
    #
    @9
    cG
    cfv
    #
    cR
    co
    @6
    cH
    @1
    wph
    cD
    cC
    @2
    cH
    ofco.3
    ffvelrnda
    wph
    vx
    cD
    cC
    cH
    ofco.3
    feqmptd
    wph
    vy
    cA
    cB
    @10
    @11
    cR
    cC
    cF
    cG
    cV
    cW
    ofco.1
    ofco.2
    ofco.4
    ofco.5
    ofco.7
    wph
    @9
    cA
    wcel
    wa
    @10
    eqidd
    wph
    @9
    cB
    wcel
    wa
    @11
    eqidd
    offval
    @9
    @3
    wceq
    @10
    @4
    @11
    @5
    cR
    @9
    @3
    cF
    fveq2
    @9
    @3
    cG
    fveq2
    oveq12d
    fmptco
    wph
    vx
    cD
    cD
    @4
    @5
    cR
    cD
    @7
    @8
    cX
    cX
    wph
    cF
    cA
    wfn
    cD
    cA
    cH
    wf
    #
    @7
    cD
    wfn
    ofco.1
    wph
    cD
    cC
    cH
    wf
    #
    cC
    cA
    wss
    @12
    ofco.3
    cC
    cA
    cB
    cin
    #
    cA
    ofco.7
    cA
    cB
    inss1
    eqsstr3i
    cD
    cC
    cA
    cH
    fss
    sylancl
    cA
    cD
    cF
    cH
    fnfco
    syl2anc
    wph
    cG
    cB
    wfn
    cD
    cB
    cH
    wf
    #
    @8
    cD
    wfn
    ofco.2
    wph
    @13
    cC
    cB
    wss
    @15
    ofco.3
    cC
    @14
    cB
    ofco.7
    cA
    cB
    inss2
    eqsstr3i
    cD
    cC
    cB
    cH
    fss
    sylancl
    cB
    cD
    cG
    cH
    fnfco
    syl2anc
    ofco.6
    ofco.6
    cD
    inidm
    wph
    cH
    cD
    wfn
    #
    @2
    cD
    wcel
    #
    @2
    @7
    cfv
    @4
    wceq
    wph
    @13
    @16
    ofco.3
    cD
    cC
    cH
    ffn
    syl
    #
    cD
    cF
    cH
    @2
    fvco2
    sylan
    wph
    @16
    @17
    @2
    @8
    cfv
    @5
    wceq
    @18
    cD
    cG
    cH
    @2
    fvco2
    sylan
    offval
    eqtr4d
end

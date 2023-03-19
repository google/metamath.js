include "cof.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cres.mm"
include "wcel.mm"
include "wa.mm"
include "eqidd.mm"
include "offval.mm"
include "cvv.mm"
include "wfn.mm"
include "wss.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstr3i.mm"
include "fnssres.mm"
include "sylancl.mm"
include "inss2.mm"
include "ssexg.mm"
include "sylancr.mm"
include "inidm.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "eqtr4d.mm"

theorem ofres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume ofres.1: |- ( ph -> F Fn A )
  assume ofres.2: |- ( ph -> G Fn B )
  assume ofres.3: |- ( ph -> A e. V )
  assume ofres.4: |- ( ph -> B e. W )
  assume ofres.5: |- ( A i^i B ) = C


  assert |- ( ph -> ( F oF R G ) = ( ( F |` C ) oF R ( G |` C ) ) )

  proof
    wph
    cF
    cG
    cR
    cof
    #
    co
    vx
    cC
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    cR
    co
    cmpt
    cF
    cC
    cres
    #
    cG
    cC
    cres
    #
    @0
    co
    wph
    vx
    cA
    cB
    @2
    @3
    cR
    cC
    cF
    cG
    cV
    cW
    ofres.1
    ofres.2
    ofres.3
    ofres.4
    ofres.5
    wph
    @1
    cA
    wcel
    wa
    @2
    eqidd
    wph
    @1
    cB
    wcel
    wa
    @3
    eqidd
    offval
    wph
    vx
    cC
    cC
    @2
    @3
    cR
    cC
    @4
    @5
    cvv
    cvv
    wph
    cF
    cA
    wfn
    cC
    cA
    wss
    #
    @4
    cC
    wfn
    ofres.1
    cC
    cA
    cB
    cin
    #
    cA
    ofres.5
    cA
    cB
    inss1
    eqsstr3i
    #
    cA
    cC
    cF
    fnssres
    sylancl
    wph
    cG
    cB
    wfn
    cC
    cB
    wss
    @5
    cC
    wfn
    ofres.2
    cC
    @7
    cB
    ofres.5
    cA
    cB
    inss2
    eqsstr3i
    cB
    cC
    cG
    fnssres
    sylancl
    wph
    @6
    cA
    cV
    wcel
    cC
    cvv
    wcel
    @8
    ofres.3
    cC
    cA
    cV
    ssexg
    sylancr
    #
    @9
    cC
    inidm
    @1
    cC
    wcel
    #
    @1
    @4
    cfv
    @2
    wceq
    wph
    @1
    cC
    cF
    fvres
    adantl
    @10
    @1
    @5
    cfv
    @3
    wceq
    wph
    @1
    cC
    cG
    fvres
    adantl
    offval
    eqtr4d
end

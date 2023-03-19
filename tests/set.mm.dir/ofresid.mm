include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cxp.mm"
include "cres.mm"
include "cof.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "fvres.mm"
include "syl.mm"
include "eqcomd.mm"
include "df-ov.mm"
include "3eqtr4g.mm"
include "mpteq2dva.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "3eqtr4d.mm"

theorem ofresid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume ofresid.1: |- ( ph -> F : A --> B )
  assume ofresid.2: |- ( ph -> G : A --> B )
  assume ofresid.3: |- ( ph -> A e. V )


  assert |- ( ph -> ( F oF R G ) = ( F oF ( R |` ( B X. B ) ) G ) )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    vx
    cA
    @1
    @2
    cR
    cB
    cB
    cxp
    #
    cres
    #
    co
    #
    cmpt
    cF
    cG
    cR
    cof
    co
    cF
    cG
    @5
    cof
    co
    wph
    vx
    cA
    @3
    @6
    wph
    @0
    cA
    wcel
    wa
    #
    @1
    @2
    cop
    #
    cR
    cfv
    #
    @8
    @5
    cfv
    #
    @3
    @6
    @7
    @10
    @9
    @7
    @8
    @4
    wcel
    #
    @10
    @9
    wceq
    @7
    @1
    cB
    wcel
    @2
    cB
    wcel
    @11
    wph
    cA
    cB
    @0
    cF
    ofresid.1
    ffvelrnda
    wph
    cA
    cB
    @0
    cG
    ofresid.2
    ffvelrnda
    @1
    @2
    cB
    cB
    opelxp
    sylanbrc
    @8
    @4
    cR
    fvres
    syl
    eqcomd
    @1
    @2
    cR
    df-ov
    @1
    @2
    @5
    df-ov
    3eqtr4g
    mpteq2dva
    wph
    vx
    cA
    cA
    @1
    @2
    cR
    cA
    cF
    cG
    cV
    cV
    wph
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    ofresid.1
    cA
    cB
    cF
    ffn
    syl
    #
    wph
    cA
    cB
    cG
    wf
    cG
    cA
    wfn
    ofresid.2
    cA
    cB
    cG
    ffn
    syl
    #
    ofresid.3
    ofresid.3
    cA
    inidm
    #
    @7
    @1
    eqidd
    #
    @7
    @2
    eqidd
    #
    offval
    wph
    vx
    cA
    cA
    @1
    @2
    @5
    cA
    cF
    cG
    cV
    cV
    @12
    @13
    ofresid.3
    ofresid.3
    @14
    @15
    @16
    offval
    3eqtr4d
end

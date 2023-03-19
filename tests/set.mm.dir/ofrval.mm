include "cofr.mm"
include "wbr.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "biimpa.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq12d.mm"
include "rspccv.mm"
include "syl.mm"
include "3impia.mm"
include "simp1.mm"
include "cin.mm"
include "inss1.mm"
include "eqsstr3i.mm"
include "simp3.mm"
include "sseldi.mm"
include "syl2anc.mm"
include "inss2.mm"
include "3brtr3d.mm"

theorem ofrval
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  assume offval.1: |- ( ph -> F Fn A )
  assume offval.2: |- ( ph -> G Fn B )
  assume offval.3: |- ( ph -> A e. V )
  assume offval.4: |- ( ph -> B e. W )
  assume offval.5: |- ( A i^i B ) = S
  assume ofval.6: |- ( ( ph /\ X e. A ) -> ( F ` X ) = C )
  assume ofval.7: |- ( ( ph /\ X e. B ) -> ( G ` X ) = D )


  assert |- ( ( ph /\ F oR R G /\ X e. S ) -> C R D )

  proof
    wph
    cF
    cG
    cR
    cofr
    wbr
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cX
    cF
    cfv
    #
    cX
    cG
    cfv
    #
    cC
    cD
    cR
    wph
    @0
    @1
    @3
    @4
    cR
    wbr
    #
    wph
    @0
    wa
    vx
    cv
    #
    cF
    cfv
    #
    @6
    cG
    cfv
    #
    cR
    wbr
    #
    vx
    cS
    wral
    #
    @1
    @5
    wi
    wph
    @0
    @10
    wph
    vx
    cA
    cB
    @7
    @8
    cR
    cS
    cF
    cG
    cV
    cW
    offval.1
    offval.2
    offval.3
    offval.4
    offval.5
    wph
    @6
    cA
    wcel
    wa
    @7
    eqidd
    wph
    @6
    cB
    wcel
    wa
    @8
    eqidd
    ofrfval
    biimpa
    @9
    @5
    vx
    cX
    cS
    @6
    cX
    wceq
    @7
    @3
    @8
    @4
    cR
    @6
    cX
    cF
    fveq2
    @6
    cX
    cG
    fveq2
    breq12d
    rspccv
    syl
    3impia
    @2
    wph
    cX
    cA
    wcel
    @3
    cC
    wceq
    wph
    @0
    @1
    simp1
    #
    @2
    cS
    cA
    cX
    cS
    cA
    cB
    cin
    #
    cA
    offval.5
    cA
    cB
    inss1
    eqsstr3i
    wph
    @0
    @1
    simp3
    #
    sseldi
    ofval.6
    syl2anc
    @2
    wph
    cX
    cB
    wcel
    @4
    cD
    wceq
    @11
    @2
    cS
    cB
    cX
    cS
    @12
    cB
    offval.5
    cA
    cB
    inss2
    eqsstr3i
    @13
    sseldi
    ofval.7
    syl2anc
    3brtr3d
end

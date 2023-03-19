include "cuni.mm"
include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "cpw.mm"
include "wa.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "sseldd.mm"
include "cfv.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "unieqi.mm"
include "eleq2i.mm"
include "elunirab.mm"
include "bitri.mm"
include "simpl.mm"
include "reximi.mm"
include "sylbi.mm"
include "r19.29a.mm"
include "a1i.mm"
include "ssrdv.mm"
include "ssid.mm"
include "ralrimiva.mm"
include "neipeltop.mm"
include "sylanbrc.mm"
include "unissel.mm"
include "syl2anc.mm"
include "eqcomd.mm"

theorem neiptopuni
  let wph: wff ph
  let cJ: class J
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cC: class C
  assume neiptop.o: |- J = { a e. ~P X | A. p e. a a e. ( N ` p ) }
  assume neiptop.0: |- ( ph -> N : X --> ~P ~P X )
  assume neiptop.1: |- ( ( ( ( ph /\ p e. X ) /\ a C_ b /\ b C_ X ) /\ a e. ( N ` p ) ) -> b e. ( N ` p ) )
  assume neiptop.2: |- ( ( ph /\ p e. X ) -> ( fi ` ( N ` p ) ) C_ ( N ` p ) )
  assume neiptop.3: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> p e. a )
  assume neiptop.4: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> E. b e. ( N ` p ) A. q e. b a e. ( N ` q ) )
  assume neiptop.5: |- ( ( ph /\ p e. X ) -> X e. ( N ` p ) )

  disjoint a p
  disjoint N a
  disjoint X a
  disjoint a b
  disjoint b p
  disjoint J a
  disjoint J p
  disjoint X p
  disjoint p ph
  disjoint C a
  disjoint C p
  assert |- ( ph -> X = U. J )

  proof
    wph
    cJ
    cuni
    #
    cX
    wph
    @0
    cX
    wss
    cX
    cJ
    wcel
    #
    @0
    cX
    wceq
    wph
    vp
    @0
    cX
    vp
    cv
    #
    @0
    wcel
    #
    @2
    cX
    wcel
    #
    wi
    wph
    @3
    @2
    va
    cv
    #
    wcel
    #
    @4
    va
    cX
    cpw
    #
    @3
    @5
    @7
    wcel
    #
    wa
    #
    @6
    wa
    @5
    cX
    @2
    @8
    @5
    cX
    wss
    @3
    @6
    @5
    cX
    elpwi
    ad2antlr
    @9
    @6
    simpr
    sseldd
    @3
    @6
    @5
    @2
    cN
    cfv
    #
    wcel
    vp
    @5
    wral
    #
    wa
    #
    va
    @7
    wrex
    #
    @6
    va
    @7
    wrex
    @3
    @2
    @11
    va
    @7
    crab
    #
    cuni
    #
    wcel
    @13
    @0
    @15
    @2
    cJ
    @14
    neiptop.o
    unieqi
    eleq2i
    @11
    va
    @2
    @7
    elunirab
    bitri
    @12
    @6
    va
    @7
    @6
    @11
    simpl
    reximi
    sylbi
    r19.29a
    a1i
    ssrdv
    wph
    cX
    cX
    wss
    #
    cX
    @10
    wcel
    #
    vp
    cX
    wral
    @1
    @16
    wph
    cX
    ssid
    a1i
    wph
    @17
    vp
    cX
    neiptop.5
    ralrimiva
    cX
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    sylanbrc
    cJ
    cX
    unissel
    syl2anc
    eqcomd
end

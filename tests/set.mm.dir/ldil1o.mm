include "wcel.mm"
include "wa.mm"
include "claut.mm"
include "cfv.mm"
include "wf1o.mm"
include "simpll.mm"
include "eqid.mm"
include "ldillaut.mm"
include "laut1o.mm"
include "syl2anc.mm"

theorem ldil1o
  let cB: class B
  let cD: class D
  let cF: class F
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume ldil1o.b: |- B = ( Base ` K )
  assume ldil1o.h: |- H = ( LHyp ` K )
  assume ldil1o.d: |- D = ( ( LDil ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. D ) -> F : B -1-1-onto-> B )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cF
    cD
    wcel
    #
    wa
    @0
    cF
    cK
    claut
    cfv
    #
    wcel
    cB
    cB
    cF
    wf1o
    @0
    @1
    @2
    simpll
    cD
    cF
    cH
    @3
    cK
    cV
    cW
    ldil1o.h
    @3
    eqid
    #
    ldil1o.d
    ldillaut
    cV
    cB
    cF
    @3
    cK
    ldil1o.b
    @4
    laut1o
    syl2anc
end

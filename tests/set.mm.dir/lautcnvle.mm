include "wcel.mm"
include "wa.mm"
include "ccnv.mm"
include "cfv.mm"
include "wbr.mm"
include "wb.mm"
include "simpl.mm"
include "wf1o.mm"
include "laut1o.mm"
include "adantr.mm"
include "simprl.mm"
include "f1ocnvdm.mm"
include "syl2anc.mm"
include "simprr.mm"
include "lautle.mm"
include "syl12anc.mm"
include "wceq.mm"
include "f1ocnvfv2.mm"
include "breq12d.mm"
include "bitr2d.mm"

theorem lautcnvle
  let cB: class B
  let cF: class F
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  assume lautcnvle.b: |- B = ( Base ` K )
  assume lautcnvle.l: |- .<_ = ( le ` K )
  assume lautcnvle.i: |- I = ( LAut ` K )


  assert |- ( ( ( K e. V /\ F e. I ) /\ ( X e. B /\ Y e. B ) ) -> ( X .<_ Y <-> ( `' F ` X ) .<_ ( `' F ` Y ) ) )

  proof
    cK
    cV
    wcel
    cF
    cI
    wcel
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cX
    cF
    ccnv
    #
    cfv
    #
    cY
    @5
    cfv
    #
    c.le
    wbr
    #
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    c.le
    wbr
    #
    cX
    cY
    c.le
    wbr
    @4
    @0
    @6
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @8
    @11
    wb
    @0
    @3
    simpl
    @4
    cB
    cB
    cF
    wf1o
    #
    @1
    @12
    @0
    @14
    @3
    cV
    cB
    cF
    cI
    cK
    lautcnvle.b
    lautcnvle.i
    laut1o
    adantr
    #
    @0
    @1
    @2
    simprl
    #
    cB
    cB
    cX
    cF
    f1ocnvdm
    syl2anc
    @4
    @14
    @2
    @13
    @15
    @0
    @1
    @2
    simprr
    #
    cB
    cB
    cY
    cF
    f1ocnvdm
    syl2anc
    cB
    cF
    cI
    cK
    c.le
    cV
    @6
    @7
    lautcnvle.b
    lautcnvle.l
    lautcnvle.i
    lautle
    syl12anc
    @4
    @9
    cX
    @10
    cY
    c.le
    @4
    @14
    @1
    @9
    cX
    wceq
    @15
    @16
    cB
    cB
    cX
    cF
    f1ocnvfv2
    syl2anc
    @4
    @14
    @2
    @10
    cY
    wceq
    @15
    @17
    cB
    cB
    cY
    cF
    f1ocnvfv2
    syl2anc
    breq12d
    bitr2d
end

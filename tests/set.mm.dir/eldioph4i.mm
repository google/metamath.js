include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cun.mm"
include "cmzp.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "cdioph.mm"
include "weq.mm"
include "uneq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "uneq2.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "cbvrabv.mm"
include "fveq1.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan2.mm"
include "anim2i.mm"
include "eldioph4b.mm"
include "sylibr.mm"

theorem eldioph4i
  let vw: setvar w
  let vt: setvar t
  let cP: class P
  let cN: class N
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vp: setvar p
  let vu: setvar u
  let cS: class S
  assume eldioph4b.a: |- W e. _V
  assume eldioph4b.b: |- -. W e. Fin
  assume eldioph4b.c: |- ( W i^i NN ) = (/)

  disjoint W t
  disjoint W w
  disjoint t w
  disjoint N t
  disjoint N w
  disjoint P t
  disjoint P w
  disjoint W a
  disjoint W b
  disjoint W p
  disjoint W u
  disjoint a b
  disjoint a p
  disjoint a u
  disjoint a t
  disjoint a w
  disjoint b p
  disjoint b u
  disjoint b t
  disjoint b w
  disjoint p u
  disjoint p t
  disjoint p w
  disjoint t u
  disjoint u w
  disjoint S a
  disjoint S b
  disjoint S p
  disjoint S u
  disjoint S t
  disjoint S w
  disjoint N a
  disjoint N b
  disjoint N p
  disjoint N u
  disjoint P a
  disjoint P b
  disjoint P p
  disjoint P u
  assert |- ( ( N e. NN0 /\ P e. ( mzPoly ` ( W u. ( 1 ... N ) ) ) ) -> { t e. ( NN0 ^m ( 1 ... N ) ) | E. w e. ( NN0 ^m W ) ( P ` ( t u. w ) ) = 0 } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    cP
    cW
    c1
    cN
    cfz
    co
    #
    cun
    cmzp
    cfv
    #
    wcel
    #
    wa
    @0
    vt
    cv
    #
    vw
    cv
    #
    cun
    #
    cP
    cfv
    #
    cc0
    wceq
    #
    vw
    cn0
    cW
    cmap
    co
    #
    wrex
    #
    vt
    cn0
    @1
    cmap
    co
    #
    crab
    #
    va
    cv
    #
    vb
    cv
    #
    cun
    #
    vp
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    vb
    @9
    wrex
    #
    va
    @11
    crab
    #
    wceq
    #
    vp
    @2
    wrex
    #
    wa
    @12
    cN
    cdioph
    cfv
    wcel
    @3
    @22
    @0
    @3
    @12
    @15
    cP
    cfv
    #
    cc0
    wceq
    #
    vb
    @9
    wrex
    #
    va
    @11
    crab
    #
    wceq
    #
    @22
    @10
    @25
    vt
    va
    @11
    vt
    va
    weq
    #
    @10
    @13
    @5
    cun
    #
    cP
    cfv
    #
    cc0
    wceq
    #
    vw
    @9
    wrex
    @25
    @28
    @8
    @31
    vw
    @9
    @28
    @7
    @30
    cc0
    @28
    @6
    @29
    cP
    @4
    @13
    @5
    uneq1
    fveq2d
    eqeq1d
    rexbidv
    @31
    @24
    vw
    vb
    @9
    vw
    vb
    weq
    #
    @30
    @23
    cc0
    @32
    @29
    @15
    cP
    @5
    @14
    @13
    uneq2
    fveq2d
    eqeq1d
    cbvrexv
    syl6bb
    cbvrabv
    @21
    @27
    vp
    cP
    @2
    @16
    cP
    wceq
    #
    @20
    @26
    @12
    @33
    @19
    @25
    va
    @11
    @33
    @18
    @24
    vb
    @9
    @33
    @17
    @23
    cc0
    @15
    @16
    cP
    fveq1
    eqeq1d
    rexbidv
    rabbidv
    eqeq2d
    rspcev
    mpan2
    anim2i
    vb
    va
    @12
    cN
    cW
    vp
    eldioph4b.a
    eldioph4b.b
    eldioph4b.c
    eldioph4b
    sylibr
end

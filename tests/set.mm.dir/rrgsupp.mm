include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "co.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "csupp.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "wceq.mm"
include "cvv.mm"
include "adantr.mm"
include "fvexd.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "feqmptd.mm"
include "offval2.mm"
include "fveq1d.mm"
include "simpr.mm"
include "ovex.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "neeq1d.mm"
include "rabbidva.mm"
include "crg.mm"
include "wb.mm"
include "ffvelrnda.mm"
include "rrgeq0.mm"
include "syl3anc.mm"
include "necon3bid.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fneq1.mm"
include "mpbiri.mm"
include "syl.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppvalfn.mm"
include "wf.mm"
include "ffn.mm"
include "3eqtr4d.mm"

theorem rrgsupp
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cE: class E
  let cI: class I
  let cV: class V
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  assume rrgval.e: |- E = ( RLReg ` R )
  assume rrgval.b: |- B = ( Base ` R )
  assume rrgval.t: |- .x. = ( .r ` R )
  assume rrgval.z: |- .0. = ( 0g ` R )
  assume rrgsupp.i: |- ( ph -> I e. V )
  assume rrgsupp.r: |- ( ph -> R e. Ring )
  assume rrgsupp.x: |- ( ph -> X e. E )
  assume rrgsupp.y: |- ( ph -> Y : I --> B )


  assert |- ( ph -> ( ( ( I X. { X } ) oF .x. Y ) supp .0. ) = ( Y supp .0. ) )

  proof
    wph
    vx
    cv
    #
    cI
    cX
    csn
    cxp
    #
    cY
    c.x
    cof
    co
    #
    cfv
    #
    c.0
    wne
    #
    vx
    cI
    crab
    #
    @0
    cY
    cfv
    #
    c.0
    wne
    #
    vx
    cI
    crab
    #
    @2
    c.0
    csupp
    co
    #
    cY
    c.0
    csupp
    co
    #
    wph
    @5
    cX
    @6
    c.x
    co
    #
    c.0
    wne
    #
    vx
    cI
    crab
    @8
    wph
    @4
    @12
    vx
    cI
    wph
    @0
    cI
    wcel
    #
    wa
    #
    @3
    @11
    c.0
    @14
    @3
    @0
    vy
    cI
    cX
    vy
    cv
    #
    cY
    cfv
    #
    c.x
    co
    #
    cmpt
    #
    cfv
    #
    @11
    @14
    @0
    @2
    @18
    wph
    @2
    @18
    wceq
    #
    @13
    wph
    vy
    cI
    cX
    @16
    c.x
    @1
    cY
    cV
    cE
    cvv
    rrgsupp.i
    wph
    cX
    cE
    wcel
    #
    @15
    cI
    wcel
    #
    rrgsupp.x
    adantr
    wph
    @22
    wa
    @15
    cY
    fvexd
    @1
    vy
    cI
    cX
    cmpt
    wceq
    wph
    vy
    cI
    cX
    fconstmpt
    a1i
    wph
    vy
    cI
    cB
    cY
    rrgsupp.y
    feqmptd
    offval2
    #
    adantr
    fveq1d
    @14
    @13
    @11
    cvv
    wcel
    @19
    @11
    wceq
    wph
    @13
    simpr
    cX
    @6
    c.x
    ovex
    vy
    @0
    @17
    @11
    cI
    cvv
    @18
    @15
    @0
    wceq
    @16
    @6
    cX
    c.x
    @15
    @0
    cY
    fveq2
    oveq2d
    @18
    eqid
    #
    fvmptg
    sylancl
    eqtrd
    neeq1d
    rabbidva
    wph
    @12
    @7
    vx
    cI
    @14
    @11
    c.0
    @6
    c.0
    @14
    cR
    crg
    wcel
    #
    @21
    @6
    cB
    wcel
    @11
    c.0
    wceq
    @6
    c.0
    wceq
    wb
    wph
    @25
    @13
    rrgsupp.r
    adantr
    wph
    @21
    @13
    rrgsupp.x
    adantr
    wph
    cI
    cB
    @0
    cY
    rrgsupp.y
    ffvelrnda
    cB
    cR
    c.x
    cE
    cX
    @6
    c.0
    rrgval.e
    rrgval.b
    rrgval.t
    rrgval.z
    rrgeq0
    syl3anc
    necon3bid
    rabbidva
    eqtrd
    wph
    @2
    cI
    wfn
    #
    cI
    cV
    wcel
    #
    c.0
    cvv
    wcel
    #
    @9
    @5
    wceq
    wph
    @20
    @26
    @23
    @20
    @26
    @18
    cI
    wfn
    vy
    cI
    @17
    @18
    cX
    @16
    c.x
    ovex
    @24
    fnmpti
    cI
    @2
    @18
    fneq1
    mpbiri
    syl
    rrgsupp.i
    @28
    wph
    c.0
    cR
    c0g
    cfv
    cvv
    rrgval.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    #
    vx
    @2
    cV
    cvv
    cI
    c.0
    suppvalfn
    syl3anc
    wph
    cY
    cI
    wfn
    #
    @27
    @28
    @10
    @8
    wceq
    wph
    cI
    cB
    cY
    wf
    @30
    rrgsupp.y
    cI
    cB
    cY
    ffn
    syl
    rrgsupp.i
    @29
    vx
    cY
    cV
    cvv
    cI
    c.0
    suppvalfn
    syl3anc
    3eqtr4d
end

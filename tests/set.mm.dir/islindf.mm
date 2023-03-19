include "wcel.mm"
include "clindf.mm"
include "wbr.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "cbs.mm"
include "cvsca.mm"
include "clspn.mm"
include "c0g.mm"
include "csca.mm"
include "wsbc.mm"
include "wceq.mm"
include "feq1.mm"
include "adantr.mm"
include "dmeq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "feq23d.mm"
include "bitrd.mm"
include "fvex.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "raleqdv.mm"
include "ralbidv.mm"
include "sbcie.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "fveq1.mm"
include "oveq123d.mm"
include "imaeq1.mm"
include "difeq1d.mm"
include "imaeq2d.mm"
include "eqtrd.mm"
include "fveq12d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "df-lindf.mm"
include "brabga.mm"
include "ancoms.mm"

theorem islindf
  let vx: setvar x
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vf: setvar f
  let vw: setvar w
  let vs: setvar s
  assume islindf.b: |- B = ( Base ` W )
  assume islindf.v: |- .x. = ( .s ` W )
  assume islindf.k: |- K = ( LSpan ` W )
  assume islindf.s: |- S = ( Scalar ` W )
  assume islindf.n: |- N = ( Base ` S )
  assume islindf.z: |- .0. = ( 0g ` S )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint N k
  disjoint W k
  disjoint W x
  disjoint .0. k
  disjoint B f
  disjoint B w
  disjoint f w
  disjoint F f
  disjoint F w
  disjoint f k
  disjoint f x
  disjoint k w
  disjoint w x
  disjoint K f
  disjoint K w
  disjoint N f
  disjoint N w
  disjoint .x. f
  disjoint .x. w
  disjoint W f
  disjoint W w
  disjoint .0. f
  disjoint .0. w
  disjoint f s
  disjoint k s
  disjoint s w
  disjoint s x
  assert |- ( ( W e. Y /\ F e. X ) -> ( F LIndF W <-> ( F : dom F --> B /\ A. x e. dom F A. k e. ( N \ { .0. } ) -. ( k .x. ( F ` x ) ) e. ( K ` ( F " ( dom F \ { x } ) ) ) ) ) )

  proof
    cF
    cX
    wcel
    cW
    cY
    wcel
    cF
    cW
    clindf
    wbr
    cF
    cdm
    #
    cB
    cF
    wf
    #
    vk
    cv
    #
    vx
    cv
    #
    cF
    cfv
    #
    c.x
    co
    #
    cF
    @0
    @3
    csn
    #
    cdif
    #
    cima
    #
    cK
    cfv
    #
    wcel
    #
    wn
    #
    vk
    cN
    c.0
    csn
    #
    cdif
    #
    wral
    #
    vx
    @0
    wral
    #
    wa
    #
    wb
    vf
    cv
    #
    cdm
    #
    vw
    cv
    #
    cbs
    cfv
    #
    @17
    wf
    #
    @2
    @3
    @17
    cfv
    #
    @19
    cvsca
    cfv
    #
    co
    #
    @17
    @18
    @6
    cdif
    #
    cima
    #
    @19
    clspn
    cfv
    #
    cfv
    #
    wcel
    #
    wn
    #
    vk
    vs
    cv
    #
    cbs
    cfv
    #
    @31
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    @18
    wral
    #
    vs
    @19
    csca
    cfv
    #
    wsbc
    #
    wa
    @16
    vf
    vw
    cF
    cW
    clindf
    cX
    cY
    @17
    cF
    wceq
    #
    @19
    cW
    wceq
    #
    wa
    #
    @21
    @1
    @39
    @15
    @42
    @21
    @18
    @20
    cF
    wf
    #
    @1
    @40
    @21
    @43
    wb
    @41
    @18
    @20
    @17
    cF
    feq1
    adantr
    @42
    @18
    @20
    @0
    cB
    cF
    @40
    @18
    @0
    wceq
    @41
    @17
    cF
    dmeq
    #
    adantr
    #
    @41
    @20
    cB
    wceq
    @40
    @41
    @20
    cW
    cbs
    cfv
    cB
    @19
    cW
    cbs
    fveq2
    islindf.b
    syl6eqr
    adantl
    feq23d
    bitrd
    @39
    @30
    vk
    @38
    cbs
    cfv
    #
    @38
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    vx
    @18
    wral
    #
    @42
    @15
    @37
    @51
    vs
    @38
    @19
    csca
    fvex
    @31
    @38
    wceq
    #
    @36
    @50
    vx
    @18
    @52
    @30
    vk
    @35
    @49
    @52
    @32
    @46
    @34
    @48
    @31
    @38
    cbs
    fveq2
    @52
    @33
    @47
    @31
    @38
    c0g
    fveq2
    sneqd
    difeq12d
    raleqdv
    ralbidv
    sbcie
    @42
    @50
    @14
    vx
    @18
    @0
    @45
    @42
    @30
    @11
    vk
    @49
    @13
    @41
    @49
    @13
    wceq
    @40
    @41
    @46
    cN
    @48
    @12
    @41
    @46
    cS
    cbs
    cfv
    cN
    @41
    @38
    cS
    cbs
    @41
    @38
    cW
    csca
    cfv
    cS
    @19
    cW
    csca
    fveq2
    islindf.s
    syl6eqr
    #
    fveq2d
    islindf.n
    syl6eqr
    @41
    @47
    c.0
    @41
    @47
    cS
    c0g
    cfv
    c.0
    @41
    @38
    cS
    c0g
    @53
    fveq2d
    islindf.z
    syl6eqr
    sneqd
    difeq12d
    adantl
    @42
    @29
    @10
    @42
    @24
    @5
    @28
    @9
    @42
    @2
    @2
    @22
    @4
    @23
    c.x
    @41
    @23
    c.x
    wceq
    @40
    @41
    @23
    cW
    cvsca
    cfv
    c.x
    @19
    cW
    cvsca
    fveq2
    islindf.v
    syl6eqr
    adantl
    @42
    @2
    eqidd
    @40
    @22
    @4
    wceq
    @41
    @3
    @17
    cF
    fveq1
    adantr
    oveq123d
    @42
    @26
    @8
    @27
    cK
    @41
    @27
    cK
    wceq
    @40
    @41
    @27
    cW
    clspn
    cfv
    cK
    @19
    cW
    clspn
    fveq2
    islindf.k
    syl6eqr
    adantl
    @40
    @26
    @8
    wceq
    @41
    @40
    @26
    cF
    @25
    cima
    @8
    @17
    cF
    @25
    imaeq1
    @40
    @25
    @7
    cF
    @40
    @18
    @0
    @6
    @44
    difeq1d
    imaeq2d
    eqtrd
    adantr
    fveq12d
    eleq12d
    notbid
    raleqbidv
    raleqbidv
    syl5bb
    anbi12d
    vx
    vw
    vf
    vk
    vs
    df-lindf
    brabga
    ancoms
end

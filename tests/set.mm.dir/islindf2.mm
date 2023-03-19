include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "clindf.mm"
include "wbr.mm"
include "cdm.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "fex.mm"
include "syl2anc.mm"
include "islindf.mm"
include "wss.mm"
include "ffdm.mm"
include "simpld.mm"
include "3ad2ant3.mm"
include "biantrurd.mm"
include "wceq.mm"
include "fdm.mm"
include "difeq1d.mm"
include "imaeq2d.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "3bitr2d.mm"

theorem islindf2
  let vx: setvar x
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cI: class I
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
  disjoint B k
  disjoint B x
  disjoint I k
  disjoint I x
  disjoint X k
  disjoint X x
  disjoint Y k
  disjoint Y x
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
  assert |- ( ( W e. Y /\ I e. X /\ F : I --> B ) -> ( F LIndF W <-> A. x e. I A. k e. ( N \ { .0. } ) -. ( k .x. ( F ` x ) ) e. ( K ` ( F " ( I \ { x } ) ) ) ) )

  proof
    cW
    cY
    wcel
    #
    cI
    cX
    wcel
    #
    cI
    cB
    cF
    wf
    #
    w3a
    #
    cF
    cW
    clindf
    wbr
    #
    cF
    cdm
    #
    cB
    cF
    wf
    #
    vk
    cv
    vx
    cv
    #
    cF
    cfv
    c.x
    co
    #
    cF
    @5
    @7
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
    cdif
    #
    wral
    #
    vx
    @5
    wral
    #
    wa
    #
    @17
    @8
    cF
    cI
    @9
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
    @15
    wral
    #
    vx
    cI
    wral
    @3
    @0
    cF
    cvv
    wcel
    #
    @4
    @18
    wb
    @0
    @1
    @2
    simp1
    @3
    @2
    @1
    @25
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    cI
    cB
    cX
    cF
    fex
    syl2anc
    vx
    cB
    cS
    c.x
    vk
    cF
    cK
    cN
    cW
    cvv
    cY
    c.0
    islindf.b
    islindf.v
    islindf.k
    islindf.s
    islindf.n
    islindf.z
    islindf
    syl2anc
    @3
    @6
    @17
    @2
    @0
    @6
    @1
    @2
    @6
    @5
    cI
    wss
    cI
    cB
    cF
    ffdm
    simpld
    3ad2ant3
    biantrurd
    @3
    @16
    @24
    vx
    @5
    cI
    @2
    @0
    @5
    cI
    wceq
    @1
    cI
    cB
    cF
    fdm
    3ad2ant3
    #
    @3
    @14
    @23
    vk
    @15
    @3
    @13
    @22
    @3
    @12
    @21
    @8
    @3
    @11
    @20
    cK
    @3
    @10
    @19
    cF
    @3
    @5
    cI
    @9
    @26
    difeq1d
    imaeq2d
    fveq2d
    eleq2d
    notbid
    ralbidv
    raleqbidv
    3bitr2d
end

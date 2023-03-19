include "wcel.mm"
include "clinds.mm"
include "cfv.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "clindf.mm"
include "wbr.mm"
include "wa.mm"
include "cdm.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wn.mm"
include "wral.mm"
include "islinds.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "adantl.mm"
include "resiexg.mm"
include "syl.mm"
include "islindf.mm"
include "syldan.mm"
include "pm5.32da.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "dmresi.mm"
include "feq2i.mm"
include "mpbir.mm"
include "fss.mm"
include "mpan.mm"
include "biantrurd.mm"
include "raleqi.mm"
include "fvresi.mm"
include "oveq2d.mm"
include "wceq.mm"
include "difeq1i.mm"
include "imaeq2i.mm"
include "difss.mm"
include "resiima.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "a1i.mm"
include "eleq12d.mm"
include "notbid.mm"
include "ralbidv.mm"
include "ralbiia.mm"
include "bitri.mm"
include "anbi2i.mm"
include "syl6rbbr.mm"
include "pm5.32i.mm"
include "3bitrd.mm"

theorem islinds2
  let vx: setvar x
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cN: class N
  let cW: class W
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
  assert |- ( W e. Y -> ( F e. ( LIndS ` W ) <-> ( F C_ B /\ A. x e. F A. k e. ( N \ { .0. } ) -. ( k .x. x ) e. ( K ` ( F \ { x } ) ) ) ) )

  proof
    cW
    cY
    wcel
    #
    cF
    cW
    clinds
    cfv
    wcel
    cF
    cB
    wss
    #
    cid
    cF
    cres
    #
    cW
    clindf
    wbr
    #
    wa
    @1
    @2
    cdm
    #
    cB
    @2
    wf
    #
    vk
    cv
    #
    vx
    cv
    #
    @2
    cfv
    #
    c.x
    co
    #
    @2
    @4
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
    @4
    wral
    #
    wa
    #
    wa
    #
    @1
    @6
    @7
    c.x
    co
    #
    cF
    @10
    cdif
    #
    cK
    cfv
    #
    wcel
    #
    wn
    #
    vk
    @16
    wral
    #
    vx
    cF
    wral
    #
    wa
    #
    cB
    cY
    cW
    cF
    islindf.b
    islinds
    @0
    @1
    @3
    @19
    @0
    @1
    @2
    cvv
    wcel
    #
    @3
    @19
    wb
    @0
    @1
    wa
    cF
    cvv
    wcel
    #
    @29
    @1
    @30
    @0
    cF
    cB
    cB
    cW
    cbs
    cfv
    cvv
    islindf.b
    cW
    cbs
    fvex
    eqeltri
    ssex
    adantl
    cF
    cvv
    resiexg
    syl
    vx
    cB
    cS
    c.x
    vk
    @2
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
    syldan
    pm5.32da
    @20
    @28
    wb
    @0
    @1
    @19
    @27
    @1
    @27
    @5
    @27
    wa
    @19
    @1
    @5
    @27
    @4
    cF
    @2
    wf
    #
    @1
    @5
    @31
    cF
    cF
    @2
    wf
    #
    cF
    cF
    @2
    wf1o
    @32
    cF
    f1oi
    cF
    cF
    @2
    f1of
    ax-mp
    @4
    cF
    cF
    @2
    cF
    dmresi
    #
    feq2i
    mpbir
    @4
    cF
    cB
    @2
    fss
    mpan
    biantrurd
    @18
    @27
    @5
    @18
    @17
    vx
    cF
    wral
    @27
    @17
    vx
    @4
    cF
    @33
    raleqi
    @17
    @26
    vx
    cF
    @7
    cF
    wcel
    #
    @15
    @25
    vk
    @16
    @34
    @14
    @24
    @34
    @9
    @21
    @13
    @23
    @34
    @8
    @7
    @6
    c.x
    cF
    @7
    fvresi
    oveq2d
    @13
    @23
    wceq
    @34
    @12
    @22
    cK
    @12
    @2
    @22
    cima
    #
    @22
    @11
    @22
    @2
    @4
    cF
    @10
    @33
    difeq1i
    imaeq2i
    @22
    cF
    wss
    @35
    @22
    wceq
    cF
    @10
    difss
    cF
    @22
    resiima
    ax-mp
    eqtri
    fveq2i
    a1i
    eleq12d
    notbid
    ralbidv
    ralbiia
    bitri
    anbi2i
    syl6rbbr
    pm5.32i
    a1i
    3bitrd
end

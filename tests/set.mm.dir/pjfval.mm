include "cpj.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cvv.mm"
include "cmap.mm"
include "cxp.mm"
include "cin.mm"
include "wcel.mm"
include "wceq.mm"
include "clss.mm"
include "cocv.mm"
include "cpj1.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "oveq12d.mm"
include "xpeq2d.mm"
include "ineq12d.mm"
include "df-pj.mm"
include "fvex.mm"
include "eqeltri.mm"
include "inex1.mm"
include "ovex.mm"
include "inex2.mm"
include "xpex.mm"
include "wf.mm"
include "wss.mm"
include "eqid.mm"
include "ovexd.mm"
include "fmpti.mm"
include "fssxp.mm"
include "ssrin.mm"
include "mp2b.mm"
include "inxp.mm"
include "sseqtri.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "inss1.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "sseq0.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem pjfval
  let vx: setvar x
  let cP: class P
  let cK: class K
  let cL: class L
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vb: setvar b
  let vh: setvar h
  let vy: setvar y
  let vw: setvar w
  let cT: class T
  assume pjfval.v: |- V = ( Base ` W )
  assume pjfval.l: |- L = ( LSubSp ` W )
  assume pjfval.o: |- ._|_ = ( ocv ` W )
  assume pjfval.p: |- P = ( proj1 ` W )
  assume pjfval.k: |- K = ( proj ` W )

  disjoint ._|_ x
  disjoint L x
  disjoint P x
  disjoint V x
  disjoint W x
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint w x
  disjoint ._|_ w
  disjoint L w
  disjoint P w
  disjoint V w
  disjoint W w
  disjoint T x
  assert |- K = ( ( x e. L |-> ( x P ( ._|_ ` x ) ) ) i^i ( _V X. ( V ^m V ) ) )

  proof
    cK
    cW
    cpj
    cfv
    #
    vx
    cL
    vx
    cv
    #
    @1
    c.pe
    cfv
    #
    cP
    co
    #
    cmpt
    #
    cvv
    cV
    cV
    cmap
    co
    #
    cxp
    #
    cin
    #
    pjfval.k
    cW
    cvv
    wcel
    #
    @0
    @7
    wceq
    vw
    cW
    vx
    vw
    cv
    #
    clss
    cfv
    #
    @1
    @1
    @9
    cocv
    cfv
    #
    cfv
    #
    @9
    cpj1
    cfv
    #
    co
    #
    cmpt
    #
    cvv
    @9
    cbs
    cfv
    #
    @16
    cmap
    co
    #
    cxp
    #
    cin
    @7
    cvv
    cpj
    @9
    cW
    wceq
    #
    @15
    @4
    @18
    @6
    @19
    vx
    @10
    @14
    cL
    @3
    @19
    @10
    cW
    clss
    cfv
    #
    cL
    @9
    cW
    clss
    fveq2
    pjfval.l
    syl6eqr
    @19
    @1
    @1
    @12
    @2
    @13
    cP
    @19
    @13
    cW
    cpj1
    cfv
    cP
    @9
    cW
    cpj1
    fveq2
    pjfval.p
    syl6eqr
    @19
    @1
    eqidd
    @19
    @1
    @11
    c.pe
    @19
    @11
    cW
    cocv
    cfv
    c.pe
    @9
    cW
    cocv
    fveq2
    pjfval.o
    syl6eqr
    fveq1d
    oveq123d
    mpteq12dv
    @19
    @17
    @5
    cvv
    @19
    @16
    cV
    @16
    cV
    cmap
    @19
    @16
    cW
    cbs
    cfv
    cV
    @9
    cW
    cbs
    fveq2
    pjfval.v
    syl6eqr
    #
    @21
    oveq12d
    xpeq2d
    ineq12d
    vx
    vw
    df-pj
    @7
    cL
    cvv
    cin
    #
    cvv
    @5
    cin
    #
    cxp
    #
    @22
    @23
    cL
    cvv
    cL
    @20
    cvv
    pjfval.l
    cW
    clss
    fvex
    eqeltri
    inex1
    @5
    cvv
    cV
    cV
    cmap
    ovex
    inex2
    xpex
    @7
    cL
    cvv
    cxp
    #
    @6
    cin
    #
    @24
    cL
    cvv
    @4
    wf
    @4
    @25
    wss
    @7
    @26
    wss
    vx
    cL
    cvv
    @3
    @4
    @4
    eqid
    @1
    cL
    wcel
    @1
    @2
    cP
    ovexd
    fmpti
    cL
    cvv
    @4
    fssxp
    @4
    @25
    @6
    ssrin
    mp2b
    cL
    cvv
    cvv
    @5
    inxp
    sseqtri
    ssexi
    fvmpt
    @8
    wn
    #
    @0
    c0
    @7
    cW
    cpj
    fvprc
    @27
    @7
    @4
    wss
    @4
    c0
    wceq
    @7
    c0
    wceq
    @4
    @6
    inss1
    @27
    @4
    vx
    c0
    @3
    cmpt
    c0
    @27
    vx
    cL
    c0
    @3
    @27
    cL
    @20
    c0
    pjfval.l
    cW
    clss
    fvprc
    syl5eq
    mpteq1d
    vx
    @3
    mpt0
    syl6eq
    @7
    @4
    sseq0
    sylancr
    eqtr4d
    pm2.61i
    eqtri
end

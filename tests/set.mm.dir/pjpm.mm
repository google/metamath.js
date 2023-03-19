include "cmap.mm"
include "co.mm"
include "cpm.mm"
include "wcel.mm"
include "wfun.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "cocv.mm"
include "cfv.mm"
include "cpj1.mm"
include "cmpt.mm"
include "cvv.mm"
include "cin.mm"
include "eqid.mm"
include "pjfval.mm"
include "inss1.mm"
include "eqsstri.mm"
include "funmpt.mm"
include "funss.mm"
include "mp2.mm"
include "wf.mm"
include "ovexd.mm"
include "fmpti.mm"
include "fssxp.mm"
include "ssrin.mm"
include "mp2b.mm"
include "inxp.mm"
include "inv1.mm"
include "incom.mm"
include "eqtri.mm"
include "xpeq12i.mm"
include "sseqtri.mm"
include "ovex.mm"
include "clss.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpm.mm"
include "mpbir2an.mm"

theorem pjpm
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume pjpm.v: |- V = ( Base ` W )
  assume pjpm.l: |- L = ( LSubSp ` W )
  assume pjpm.k: |- K = ( proj ` W )


  assert |- K e. ( ( V ^m V ) ^pm L )

  proof
    cK
    cV
    cV
    cmap
    co
    #
    cL
    cpm
    co
    wcel
    cK
    wfun
    #
    cK
    cL
    @0
    cxp
    #
    wss
    cK
    vx
    cL
    vx
    cv
    #
    @3
    cW
    cocv
    cfv
    #
    cfv
    #
    cW
    cpj1
    cfv
    #
    co
    #
    cmpt
    #
    wss
    @8
    wfun
    @1
    cK
    @8
    cvv
    @0
    cxp
    #
    cin
    #
    @8
    vx
    @6
    cK
    cL
    @4
    cV
    cW
    pjpm.v
    pjpm.l
    @4
    eqid
    @6
    eqid
    pjpm.k
    pjfval
    #
    @8
    @9
    inss1
    eqsstri
    vx
    cL
    @7
    funmpt
    cK
    @8
    funss
    mp2
    cK
    cL
    cvv
    cxp
    #
    @9
    cin
    #
    @2
    cK
    @10
    @13
    @11
    cL
    cvv
    @8
    wf
    @8
    @12
    wss
    @10
    @13
    wss
    vx
    cL
    cvv
    @7
    @8
    @8
    eqid
    @3
    cL
    wcel
    @3
    @5
    @6
    ovexd
    fmpti
    cL
    cvv
    @8
    fssxp
    @8
    @12
    @9
    ssrin
    mp2b
    eqsstri
    @13
    cL
    cvv
    cin
    #
    cvv
    @0
    cin
    #
    cxp
    @2
    cL
    cvv
    cvv
    @0
    inxp
    @14
    cL
    @15
    @0
    cL
    inv1
    @15
    @0
    cvv
    cin
    @0
    cvv
    @0
    incom
    @0
    inv1
    eqtri
    xpeq12i
    eqtri
    sseqtri
    @0
    cL
    cK
    cV
    cV
    cmap
    ovex
    cL
    cW
    clss
    cfv
    cvv
    pjpm.l
    cW
    clss
    fvex
    eqeltri
    elpm
    mpbir2an
end

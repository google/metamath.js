include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "ccld.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "wceq.mm"
include "clsfval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "wb.mm"
include "topopn.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "wrex.mm"
include "topcld.mm"
include "sseq2.mm"
include "rspcev.mm"
include "sylan.mm"
include "intexrab.mm"
include "sylib.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem clsval
  let vx: setvar x
  let cS: class S
  let cJ: class J
  let cX: class X
  let vy: setvar y
  assume iscld.1: |- X = U. J

  disjoint J x
  disjoint S x
  disjoint X x
  disjoint x y
  disjoint J y
  disjoint S y
  disjoint X y
  assert |- ( ( J e. Top /\ S C_ X ) -> ( ( cls ` J ) ` S ) = |^| { x e. ( Clsd ` J ) | S C_ x } )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    wa
    #
    cS
    cJ
    ccl
    cfv
    #
    cfv
    #
    cS
    vy
    cX
    cpw
    #
    vy
    cv
    #
    vx
    cv
    #
    wss
    #
    vx
    cJ
    ccld
    cfv
    #
    crab
    #
    cint
    #
    cmpt
    #
    cfv
    #
    cS
    @7
    wss
    #
    vx
    @9
    crab
    #
    cint
    #
    @0
    @4
    @13
    wceq
    @1
    @0
    cS
    @3
    @12
    vy
    vx
    cJ
    cX
    iscld.1
    clsfval
    fveq1d
    adantr
    @2
    cS
    @5
    wcel
    #
    @16
    cvv
    wcel
    #
    @13
    @16
    wceq
    @0
    @17
    @1
    @0
    cX
    cJ
    wcel
    @17
    @1
    wb
    cJ
    cX
    iscld.1
    topopn
    cS
    cX
    cJ
    elpw2g
    syl
    biimpar
    @2
    @14
    vx
    @9
    wrex
    #
    @18
    @0
    cX
    @9
    wcel
    @1
    @19
    cJ
    cX
    iscld.1
    topcld
    @14
    @1
    vx
    cX
    @9
    @7
    cX
    cS
    sseq2
    rspcev
    sylan
    @14
    vx
    @9
    intexrab
    sylib
    vy
    cS
    @11
    @16
    @5
    cvv
    @12
    @6
    cS
    wceq
    #
    @10
    @15
    @20
    @8
    @14
    vx
    @9
    @6
    cS
    @7
    sseq1
    rabbidv
    inteqd
    @12
    eqid
    fvmptg
    syl2anc
    eqtrd
end

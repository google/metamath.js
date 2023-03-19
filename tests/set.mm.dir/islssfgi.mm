include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "cfn.mm"
include "w3a.mm"
include "clfig.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "biimpri.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "elind.mm"
include "eqid.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "clss.mm"
include "wb.mm"
include "simp1.mm"
include "lspcl.mm"
include "3adant3.mm"
include "islssfg2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem islssfgi
  let cB: class B
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let va: setvar a
  assume islssfgi.n: |- N = ( LSpan ` W )
  assume islssfgi.v: |- V = ( Base ` W )
  assume islssfgi.x: |- X = ( W |`s ( N ` B ) )


  assert |- ( ( W e. LMod /\ B C_ V /\ B e. Fin ) -> X e. LFinGen )

  proof
    cW
    clmod
    wcel
    #
    cB
    cV
    wss
    #
    cB
    cfn
    wcel
    #
    w3a
    #
    cX
    clfig
    wcel
    #
    va
    cv
    #
    cN
    cfv
    #
    cB
    cN
    cfv
    #
    wceq
    #
    va
    cV
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @3
    cB
    @10
    wcel
    @7
    @7
    wceq
    #
    @11
    @3
    @9
    cfn
    cB
    @1
    @0
    cB
    @9
    wcel
    #
    @2
    @13
    @1
    cB
    cV
    cV
    cW
    cbs
    cfv
    cvv
    islssfgi.v
    cW
    cbs
    fvex
    eqeltri
    elpw2
    biimpri
    3ad2ant2
    @0
    @1
    @2
    simp3
    elind
    @7
    eqid
    @8
    @12
    va
    cB
    @10
    @5
    cB
    wceq
    @6
    @7
    @7
    @5
    cB
    cN
    fveq2
    eqeq1d
    rspcev
    sylancl
    @3
    @0
    @7
    cW
    clss
    cfv
    #
    wcel
    #
    @4
    @11
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @15
    @2
    @14
    cB
    cN
    cV
    cW
    islssfgi.v
    @14
    eqid
    #
    islssfgi.n
    lspcl
    3adant3
    cV
    @14
    @7
    cN
    cW
    cX
    va
    islssfgi.x
    @16
    islssfgi.n
    islssfgi.v
    islssfg2
    syl2anc
    mpbird
end

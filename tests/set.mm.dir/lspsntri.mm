include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "csn.mm"
include "cfv.mm"
include "cun.mm"
include "cpr.mm"
include "lspvadd.mm"
include "df-pr.mm"
include "fveq2i.mm"
include "syl6sseq.mm"
include "wss.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "snssd.mm"
include "simp3.mm"
include "lsmsp2.mm"
include "syl3anc.mm"
include "sseqtr4d.mm"

theorem lspsntri
  let c.pl: class .+
  let c.po: class .(+)
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspsntri.v: |- V = ( Base ` W )
  assume lspsntri.a: |- .+ = ( +g ` W )
  assume lspsntri.n: |- N = ( LSpan ` W )
  assume lspsntri.p: |- .(+) = ( LSSum ` W )


  assert |- ( ( W e. LMod /\ X e. V /\ Y e. V ) -> ( N ` { ( X .+ Y ) } ) C_ ( ( N ` { X } ) .(+) ( N ` { Y } ) ) )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cY
    c.pl
    co
    csn
    cN
    cfv
    #
    cX
    csn
    #
    cY
    csn
    #
    cun
    #
    cN
    cfv
    #
    @5
    cN
    cfv
    @6
    cN
    cfv
    c.po
    co
    #
    @3
    @4
    cX
    cY
    cpr
    #
    cN
    cfv
    @8
    c.pl
    cN
    cV
    cW
    cX
    cY
    lspsntri.v
    lspsntri.a
    lspsntri.n
    lspvadd
    @10
    @7
    cN
    cX
    cY
    df-pr
    fveq2i
    syl6sseq
    @3
    @0
    @5
    cV
    wss
    @6
    cV
    wss
    @9
    @8
    wceq
    @0
    @1
    @2
    simp1
    @3
    cX
    cV
    @0
    @1
    @2
    simp2
    snssd
    @3
    cY
    cV
    @0
    @1
    @2
    simp3
    snssd
    c.po
    @5
    @6
    cN
    cV
    cW
    lspsntri.v
    lspsntri.n
    lspsntri.p
    lsmsp2
    syl3anc
    sseqtr4d
end

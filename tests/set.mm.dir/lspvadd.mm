include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "clss.mm"
include "cfv.mm"
include "cpr.mm"
include "co.mm"
include "eqid.mm"
include "simp1.mm"
include "wss.mm"
include "prssi.mm"
include "3adant1.mm"
include "lspcl.mm"
include "syl2anc.mm"
include "wa.mm"
include "lspssid.mm"
include "wb.mm"
include "prssg.mm"
include "mpbird.mm"
include "lssvacl.mm"
include "syl21anc.mm"
include "lspsnel5a.mm"

theorem lspvadd
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspvadd.v: |- V = ( Base ` W )
  assume lspvadd.a: |- .+ = ( +g ` W )
  assume lspvadd.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ X e. V /\ Y e. V ) -> ( N ` { ( X .+ Y ) } ) C_ ( N ` { X , Y } ) )

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
    cW
    clss
    cfv
    #
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    cN
    cW
    cX
    cY
    c.pl
    co
    #
    @4
    eqid
    #
    lspvadd.n
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    @5
    cV
    wss
    #
    @6
    @4
    wcel
    #
    @9
    @1
    @2
    @10
    @0
    cX
    cY
    cV
    prssi
    3adant1
    #
    @4
    @5
    cN
    cV
    cW
    lspvadd.v
    @8
    lspvadd.n
    lspcl
    syl2anc
    #
    @3
    @0
    @11
    cX
    @6
    wcel
    cY
    @6
    wcel
    wa
    #
    @7
    @6
    wcel
    @9
    @13
    @3
    @14
    @5
    @6
    wss
    #
    @3
    @0
    @10
    @15
    @9
    @12
    @5
    cN
    cV
    cW
    lspvadd.v
    lspvadd.n
    lspssid
    syl2anc
    @1
    @2
    @14
    @15
    wb
    @0
    cX
    cY
    @6
    cV
    cV
    prssg
    3adant1
    mpbird
    c.pl
    @4
    @6
    cW
    cX
    cY
    lspvadd.a
    @8
    lssvacl
    syl21anc
    lspsnel5a
end

include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "lspsnid.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "elsni.mm"
include "syl6.mm"
include "lspsn0.mm"
include "adantr.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem lspsneq0
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lspsneq0.v: |- V = ( Base ` W )
  assume lspsneq0.z: |- .0. = ( 0g ` W )
  assume lspsneq0.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( ( N ` { X } ) = { .0. } <-> X = .0. ) )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cX
    csn
    #
    cN
    cfv
    #
    c.0
    csn
    #
    wceq
    #
    cX
    c.0
    wceq
    #
    @2
    @6
    cX
    @5
    wcel
    #
    @7
    @2
    cX
    @4
    wcel
    @6
    @8
    cN
    cV
    cW
    cX
    lspsneq0.v
    lspsneq0.n
    lspsnid
    @4
    @5
    cX
    eleq2
    syl5ibcom
    cX
    c.0
    elsni
    syl6
    @2
    @6
    @7
    @5
    cN
    cfv
    #
    @5
    wceq
    #
    @0
    @10
    @1
    cN
    cW
    c.0
    lspsneq0.z
    lspsneq0.n
    lspsn0
    adantr
    @7
    @4
    @9
    @5
    @7
    @3
    @5
    cN
    cX
    c.0
    sneq
    fveq2d
    eqeq1d
    syl5ibrcom
    impbid
end

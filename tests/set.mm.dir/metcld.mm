include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccld.mm"
include "ccl.mm"
include "cn.mm"
include "cv.mm"
include "wf.mm"
include "clm.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "ctop.mm"
include "cuni.mm"
include "wb.mm"
include "mopntop.mm"
include "adantr.mm"
include "mopnuni.mm"
include "sseq2d.mm"
include "biimpa.mm"
include "eqid.mm"
include "iscld4.mm"
include "syl2anc.mm"
include "wex.mm"
include "simpl.mm"
include "simpr.mm"
include "metelcls.mm"
include "imbi1d.mm"
include "19.23v.mm"
include "syl6rbbr.mm"
include "albidv.mm"
include "dfss2.mm"
include "syl6bbr.mm"
include "bitr4d.mm"

theorem metcld
  let vx: setvar x
  let cD: class D
  let cS: class S
  let vf: setvar f
  let cJ: class J
  let cX: class X
  assume metcld.2: |- J = ( MetOpen ` D )

  disjoint f x
  disjoint D f
  disjoint D x
  disjoint J f
  disjoint J x
  disjoint S f
  disjoint S x
  disjoint X f
  disjoint X x
  assert |- ( ( D e. ( *Met ` X ) /\ S C_ X ) -> ( S e. ( Clsd ` J ) <-> A. x A. f ( ( f : NN --> S /\ f ( ~~>t ` J ) x ) -> x e. S ) ) )

  proof
    cD
    cX
    cxmt
    cfv
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
    ccld
    cfv
    wcel
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    wss
    #
    cn
    cS
    vf
    cv
    #
    wf
    @6
    vx
    cv
    #
    cJ
    clm
    cfv
    wbr
    wa
    #
    @7
    cS
    wcel
    #
    wi
    vf
    wal
    #
    vx
    wal
    #
    @2
    cJ
    ctop
    wcel
    #
    cS
    cJ
    cuni
    #
    wss
    #
    @3
    @5
    wb
    @0
    @12
    @1
    cD
    cJ
    cX
    metcld.2
    mopntop
    adantr
    @0
    @1
    @14
    @0
    cX
    @13
    cS
    cD
    cJ
    cX
    metcld.2
    mopnuni
    sseq2d
    biimpa
    cS
    cJ
    @13
    @13
    eqid
    iscld4
    syl2anc
    @2
    @11
    @7
    @4
    wcel
    #
    @9
    wi
    #
    vx
    wal
    @5
    @2
    @10
    @16
    vx
    @2
    @16
    @8
    vf
    wex
    #
    @9
    wi
    @10
    @2
    @15
    @17
    @9
    @2
    cD
    @7
    cS
    vf
    cJ
    cX
    metcld.2
    @0
    @1
    simpl
    @0
    @1
    simpr
    metelcls
    imbi1d
    @8
    @9
    vf
    19.23v
    syl6rbbr
    albidv
    vx
    @4
    cS
    dfss2
    syl6bbr
    bitr4d
end

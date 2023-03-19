include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "cid.mm"
include "cdm.mm"
include "cpmtr.mm"
include "eqid.mm"
include "pmtrdifellem1.mm"
include "pmtrdifellem3.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rgen.mm"

theorem pmtrdifel
  let vx: setvar x
  let vt: setvar t
  let cR: class R
  let cT: class T
  let cK: class K
  let cN: class N
  let vr: setvar r
  assume pmtrdifel.t: |- T = ran ( pmTrsp ` ( N \ { K } ) )
  assume pmtrdifel.r: |- R = ran ( pmTrsp ` N )

  disjoint r t
  disjoint r x
  disjoint t x
  disjoint K r
  disjoint N r
  disjoint N x
  disjoint R r
  disjoint T x
  assert |- A. t e. T E. r e. R A. x e. ( N \ { K } ) ( t ` x ) = ( r ` x )

  proof
    vx
    cv
    #
    vt
    cv
    #
    cfv
    #
    @0
    vr
    cv
    #
    cfv
    #
    wceq
    #
    vx
    cN
    cK
    csn
    cdif
    #
    wral
    #
    vr
    cR
    wrex
    #
    vt
    cT
    @1
    cT
    wcel
    @1
    cid
    cdif
    cdm
    cN
    cpmtr
    cfv
    cfv
    #
    cR
    wcel
    @2
    @0
    @9
    cfv
    #
    wceq
    #
    vx
    @6
    wral
    #
    @8
    @1
    cR
    @9
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    @9
    eqid
    #
    pmtrdifellem1
    vx
    @1
    cR
    @9
    cT
    cK
    cN
    pmtrdifel.t
    pmtrdifel.r
    @13
    pmtrdifellem3
    @7
    @12
    vr
    @9
    cR
    @3
    @9
    wceq
    #
    @5
    @11
    vx
    @6
    @14
    @4
    @10
    @2
    @0
    @3
    @9
    fveq1
    eqeq2d
    ralbidv
    rspcev
    syl2anc
    rgen
end

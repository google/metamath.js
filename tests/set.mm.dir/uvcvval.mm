include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "uvcval.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "simpr.mm"
include "cur.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem uvcvval
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vr: setvar r
  assume uvcfval.u: |- U = ( R unitVec I )
  assume uvcfval.o: |- .1. = ( 1r ` R )
  assume uvcfval.z: |- .0. = ( 0g ` R )


  assert |- ( ( ( R e. V /\ I e. W /\ J e. I ) /\ K e. I ) -> ( ( U ` J ) ` K ) = if ( K = J , .1. , .0. ) )

  proof
    cR
    cV
    wcel
    cI
    cW
    wcel
    cJ
    cI
    wcel
    w3a
    #
    cK
    cI
    wcel
    #
    wa
    #
    cK
    cJ
    cU
    cfv
    #
    cfv
    #
    cK
    vk
    cI
    vk
    cv
    #
    cJ
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cfv
    #
    cK
    cJ
    wceq
    #
    c.1
    c.0
    cif
    #
    @0
    @4
    @9
    wceq
    @1
    @0
    cK
    @3
    @8
    cR
    cU
    c.1
    vk
    cI
    cJ
    cV
    cW
    c.0
    uvcfval.u
    uvcfval.o
    uvcfval.z
    uvcval
    fveq1d
    adantr
    @2
    @1
    @11
    cvv
    wcel
    @9
    @11
    wceq
    @0
    @1
    simpr
    @10
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    uvcfval.o
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    uvcfval.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    vk
    cK
    @7
    @11
    cI
    cvv
    @8
    @5
    cK
    wceq
    @6
    @10
    c.1
    c.0
    @5
    cK
    cJ
    eqeq1
    ifbid
    @8
    eqid
    fvmptg
    sylancl
    eqtrd
end

include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "weq.mm"
include "cif.mm"
include "cmpt.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "uvcfval.mm"
include "fveq1d.mm"
include "3adant3.mm"
include "cvv.mm"
include "simp3.mm"
include "mptexg.mm"
include "3ad2ant2.mm"
include "eqeq2.mm"
include "ifbid.mm"
include "mpteq2dv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem uvcval
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vr: setvar r
  assume uvcfval.u: |- U = ( R unitVec I )
  assume uvcfval.o: |- .1. = ( 1r ` R )
  assume uvcfval.z: |- .0. = ( 0g ` R )

  disjoint .1. k
  disjoint R k
  disjoint I k
  disjoint .0. k
  disjoint J k
  disjoint .1. i
  disjoint .1. j
  disjoint .1. r
  disjoint i j
  disjoint i k
  disjoint i r
  disjoint j k
  disjoint j r
  disjoint k r
  disjoint R i
  disjoint R j
  disjoint R r
  disjoint I i
  disjoint I j
  disjoint I r
  disjoint .0. i
  disjoint .0. j
  disjoint .0. r
  disjoint J j
  assert |- ( ( R e. V /\ I e. W /\ J e. I ) -> ( U ` J ) = ( k e. I |-> if ( k = J , .1. , .0. ) ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    cJ
    cI
    wcel
    #
    w3a
    #
    cJ
    cU
    cfv
    #
    cJ
    vj
    cI
    vk
    cI
    vk
    vj
    weq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
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
    @0
    @1
    @4
    @9
    wceq
    @2
    @0
    @1
    wa
    cJ
    cU
    @8
    cR
    cU
    c.1
    vj
    vk
    cI
    cV
    cW
    c.0
    uvcfval.u
    uvcfval.o
    uvcfval.z
    uvcfval
    fveq1d
    3adant3
    @3
    @2
    @13
    cvv
    wcel
    #
    @9
    @13
    wceq
    @0
    @1
    @2
    simp3
    @1
    @0
    @14
    @2
    vk
    cI
    @12
    cW
    mptexg
    3ad2ant2
    vj
    cJ
    @7
    @13
    cI
    cvv
    @8
    vj
    cv
    #
    cJ
    wceq
    #
    vk
    cI
    @6
    @12
    @16
    @5
    @11
    c.1
    c.0
    @15
    cJ
    @10
    eqeq2
    ifbid
    mpteq2dv
    @8
    eqid
    fvmptg
    syl2anc
    eqtrd
end

include "wcel.mm"
include "wa.mm"
include "cuvc.mm"
include "co.mm"
include "weq.mm"
include "cif.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "cmpt2.mm"
include "df-uvc.mm"
include "a1i.mm"
include "simpr.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "ifeq12d.mm"
include "adantr.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "simpl.mm"
include "mptexg.mm"
include "ovmpt2d.mm"
include "syl2an.mm"
include "syl5eq.mm"

theorem uvcfval
  let cR: class R
  let cU: class U
  let c.1: class .1.
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vi: setvar i
  let vr: setvar r
  assume uvcfval.u: |- U = ( R unitVec I )
  assume uvcfval.o: |- .1. = ( 1r ` R )
  assume uvcfval.z: |- .0. = ( 0g ` R )

  disjoint .1. j
  disjoint .1. k
  disjoint j k
  disjoint R j
  disjoint R k
  disjoint I j
  disjoint I k
  disjoint .0. j
  disjoint .0. k
  disjoint .1. i
  disjoint .1. r
  disjoint i j
  disjoint i k
  disjoint i r
  disjoint j r
  disjoint k r
  disjoint R i
  disjoint R r
  disjoint I i
  disjoint I r
  disjoint .0. i
  disjoint .0. r
  assert |- ( ( R e. V /\ I e. W ) -> U = ( j e. I |-> ( k e. I |-> if ( k = j , .1. , .0. ) ) ) )

  proof
    cR
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    cU
    cR
    cI
    cuvc
    co
    #
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
    uvcfval.u
    @0
    cR
    cvv
    wcel
    #
    cI
    cvv
    wcel
    #
    @2
    @6
    wceq
    @1
    cR
    cV
    elex
    cI
    cW
    elex
    @7
    @8
    wa
    #
    vr
    vi
    cR
    cI
    cvv
    cvv
    vj
    vi
    cv
    #
    vk
    @10
    @3
    vr
    cv
    #
    cur
    cfv
    #
    @11
    c0g
    cfv
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    @6
    cuvc
    cvv
    cuvc
    vr
    vi
    cvv
    cvv
    @16
    cmpt2
    wceq
    @9
    vi
    vj
    vk
    vr
    df-uvc
    a1i
    @11
    cR
    wceq
    #
    @10
    cI
    wceq
    #
    wa
    #
    @16
    @6
    wceq
    @9
    @19
    vj
    @10
    @15
    cI
    @5
    @17
    @18
    simpr
    #
    @19
    vk
    @10
    @14
    cI
    @4
    @20
    @17
    @14
    @4
    wceq
    @18
    @17
    @3
    @12
    c.1
    @13
    c.0
    @17
    @12
    cR
    cur
    cfv
    c.1
    @11
    cR
    cur
    fveq2
    uvcfval.o
    syl6eqr
    @17
    @13
    cR
    c0g
    cfv
    c.0
    @11
    cR
    c0g
    fveq2
    uvcfval.z
    syl6eqr
    ifeq12d
    adantr
    mpteq12dv
    mpteq12dv
    adantl
    @7
    @8
    simpl
    @7
    @8
    simpr
    @8
    @6
    cvv
    wcel
    @7
    vj
    cI
    @5
    cvv
    mptexg
    adantl
    ovmpt2d
    syl2an
    syl5eq
end

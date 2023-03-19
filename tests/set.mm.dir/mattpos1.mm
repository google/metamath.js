include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "ctpos.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "tposmpt2.mm"
include "mat1.mm"
include "tposeqd.mm"
include "cv.mm"
include "wb.mm"
include "equcom.mm"
include "a1i.mm"
include "ifbid.mm"
include "mpt2eq3ia.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "tposeqi.mm"
include "3eqtr4g.mm"

theorem mattpos1
  let cA: class A
  let cR: class R
  let c.1: class .1.
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume mattpos1.a: |- A = ( N Mat R )
  assume mattpos1.o: |- .1. = ( 1r ` A )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> tpos .1. = .1. )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cA
    cur
    cfv
    #
    ctpos
    #
    @1
    c.1
    ctpos
    c.1
    @0
    vi
    vj
    cN
    cN
    vi
    vj
    weq
    #
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    cmpt2
    #
    ctpos
    vj
    vi
    cN
    cN
    @6
    cmpt2
    #
    @2
    @1
    vi
    vj
    cN
    cN
    @6
    @7
    @7
    eqid
    tposmpt2
    @0
    @1
    @7
    cA
    cR
    @4
    vi
    vj
    cN
    @5
    mattpos1.a
    @4
    eqid
    #
    @5
    eqid
    #
    mat1
    tposeqd
    @0
    @1
    vj
    vi
    cN
    cN
    vj
    vi
    weq
    #
    @4
    @5
    cif
    #
    cmpt2
    @8
    cA
    cR
    @4
    vj
    vi
    cN
    @5
    mattpos1.a
    @9
    @10
    mat1
    vj
    vi
    cN
    cN
    @12
    @6
    vj
    cv
    cN
    wcel
    vi
    cv
    cN
    wcel
    wa
    #
    @11
    @3
    @4
    @5
    @11
    @3
    wb
    @13
    vj
    vi
    equcom
    a1i
    ifbid
    mpt2eq3ia
    syl6eq
    3eqtr4a
    c.1
    @1
    mattpos1.o
    tposeqi
    mattpos1.o
    3eqtr4g
end

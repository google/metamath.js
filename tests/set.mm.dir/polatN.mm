include "col.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "polvalN.mm"
include "sylan2.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "iinxsng.mm"
include "adantl.mm"
include "ineq2d.mm"
include "cbs.mm"
include "cops.mm"
include "olop.mm"
include "eqid.mm"
include "atbase.mm"
include "opoccl.mm"
include "syl2an.mm"
include "pmapssat.mm"
include "syldan.mm"
include "sseqin2.mm"
include "sylib.mm"
include "3eqtrd.mm"

theorem polatN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let vp: setvar p
  assume polat.o: |- ._|_ = ( oc ` K )
  assume polat.a: |- A = ( Atoms ` K )
  assume polat.m: |- M = ( pmap ` K )
  assume polat.p: |- P = ( _|_P ` K )


  assert |- ( ( K e. OL /\ Q e. A ) -> ( P ` { Q } ) = ( M ` ( ._|_ ` Q ) ) )

  proof
    cK
    col
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cQ
    csn
    #
    cP
    cfv
    #
    cA
    vp
    @3
    vp
    cv
    #
    c.pe
    cfv
    #
    cM
    cfv
    #
    ciin
    #
    cin
    #
    cA
    cQ
    c.pe
    cfv
    #
    cM
    cfv
    #
    cin
    #
    @11
    @1
    @0
    @3
    cA
    wss
    @4
    @9
    wceq
    cQ
    cA
    snssi
    cA
    col
    cP
    cK
    cM
    c.pe
    @3
    vp
    polat.o
    polat.a
    polat.m
    polat.p
    polvalN
    sylan2
    @2
    @8
    @11
    cA
    @1
    @8
    @11
    wceq
    @0
    vp
    cQ
    @7
    @11
    cA
    @5
    cQ
    wceq
    @6
    @10
    cM
    @5
    cQ
    c.pe
    fveq2
    fveq2d
    iinxsng
    adantl
    ineq2d
    @2
    @11
    cA
    wss
    #
    @12
    @11
    wceq
    @0
    @1
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    @13
    @0
    cK
    cops
    wcel
    cQ
    @14
    wcel
    @15
    @1
    cK
    olop
    cA
    @14
    cQ
    cK
    @14
    eqid
    #
    polat.a
    atbase
    @14
    cK
    c.pe
    cQ
    @16
    polat.o
    opoccl
    syl2an
    cA
    @14
    col
    cK
    cM
    @10
    @16
    polat.a
    polat.m
    pmapssat
    syldan
    @11
    cA
    sseqin2
    sylib
    3eqtrd
end

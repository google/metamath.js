include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "weq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "pmat1op.mm"
include "wceq.mm"
include "ply1scl1.mm"
include "eqcomd.mm"
include "ply1scl0.mm"
include "ifeq12d.mm"
include "adantl.mm"
include "mpt2eq3dv.mm"
include "eqtrd.mm"

theorem pmat1opsc
  let cA: class A
  let cC: class C
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cN: class N
  let c.0: class .0.
  assume pmat0opsc.p: |- P = ( Poly1 ` R )
  assume pmat0opsc.c: |- C = ( N Mat P )
  assume pmat0opsc.a: |- A = ( algSc ` P )
  assume pmat0opsc.z: |- .0. = ( 0g ` R )
  assume pmat1opsc.o: |- .1. = ( 1r ` R )

  disjoint N i
  disjoint N j
  disjoint i j
  disjoint P i
  disjoint P j
  disjoint R i
  disjoint R j
  disjoint C i
  disjoint C j
  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 1r ` C ) = ( i e. N , j e. N |-> if ( i = j , ( A ` .1. ) , ( A ` .0. ) ) ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cC
    cur
    cfv
    vi
    vj
    cN
    cN
    vi
    vj
    weq
    #
    cP
    cur
    cfv
    #
    cP
    c0g
    cfv
    #
    cif
    #
    cmpt2
    vi
    vj
    cN
    cN
    @3
    c.1
    cA
    cfv
    #
    c.0
    cA
    cfv
    #
    cif
    #
    cmpt2
    cC
    cP
    cR
    @4
    vi
    vj
    cN
    @5
    pmat0opsc.p
    pmat0opsc.c
    @5
    eqid
    #
    @4
    eqid
    #
    pmat1op
    @2
    vi
    vj
    cN
    cN
    @6
    @9
    @1
    @6
    @9
    wceq
    @0
    @1
    @3
    @4
    @7
    @5
    @8
    @1
    @7
    @4
    cA
    cP
    cR
    c.1
    @4
    pmat0opsc.p
    pmat0opsc.a
    pmat1opsc.o
    @11
    ply1scl1
    eqcomd
    @1
    @8
    @5
    cA
    cP
    cR
    @5
    c.0
    pmat0opsc.p
    pmat0opsc.a
    pmat0opsc.z
    @10
    ply1scl0
    eqcomd
    ifeq12d
    adantl
    mpt2eq3dv
    eqtrd
end

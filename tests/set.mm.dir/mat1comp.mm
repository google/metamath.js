include "weq.mm"
include "cif.mm"
include "wceq.mm"
include "cv.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "eqeq2.mm"
include "cur.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "ovmpt2.mm"

theorem mat1comp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let cM: class M
  let c.0: class .0.
  assume mamumat1cl.b: |- B = ( Base ` R )
  assume mamumat1cl.r: |- ( ph -> R e. Ring )
  assume mamumat1cl.o: |- .1. = ( 1r ` R )
  assume mamumat1cl.z: |- .0. = ( 0g ` R )
  assume mamumat1cl.i: |- I = ( i e. M , j e. M |-> if ( i = j , .1. , .0. ) )
  assume mamumat1cl.m: |- ( ph -> M e. Fin )

  disjoint i j
  disjoint B i
  disjoint B j
  disjoint M i
  disjoint M j
  disjoint i ph
  disjoint j ph
  disjoint A i
  disjoint A j
  disjoint J i
  disjoint J j
  disjoint .0. i
  disjoint .0. j
  disjoint .1. i
  disjoint .1. j
  assert |- ( ( A e. M /\ J e. M ) -> ( A I J ) = if ( A = J , .1. , .0. ) )

  proof
    vi
    vj
    cA
    cJ
    cM
    cM
    vi
    vj
    weq
    #
    c.1
    c.0
    cif
    cA
    cJ
    wceq
    #
    c.1
    c.0
    cif
    cI
    cA
    vj
    cv
    #
    wceq
    #
    c.1
    c.0
    cif
    vi
    cv
    #
    cA
    wceq
    @0
    @3
    c.1
    c.0
    @4
    cA
    @2
    eqeq1
    ifbid
    @2
    cJ
    wceq
    @3
    @1
    c.1
    c.0
    @2
    cJ
    cA
    eqeq2
    ifbid
    mamumat1cl.i
    @1
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    mamumat1cl.o
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    mamumat1cl.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    ovmpt2
end

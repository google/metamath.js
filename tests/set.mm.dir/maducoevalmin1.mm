include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cur.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt2.mm"
include "cminmar1.mm"
include "eqid.mm"
include "maducoeval.mm"
include "minmar1val.mm"
include "3com23.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem maducoevalmin1
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cH: class H
  let cI: class I
  let cJ: class J
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume maducoevalmin1.a: |- A = ( N Mat R )
  assume maducoevalmin1.b: |- B = ( Base ` A )
  assume maducoevalmin1.d: |- D = ( N maDet R )
  assume maducoevalmin1.j: |- J = ( N maAdju R )


  assert |- ( ( M e. B /\ I e. N /\ H e. N ) -> ( I ( J ` M ) H ) = ( D ` ( H ( ( N minMatR1 R ) ` M ) I ) ) )

  proof
    cM
    cB
    wcel
    #
    cI
    cN
    wcel
    #
    cH
    cN
    wcel
    #
    w3a
    #
    cI
    cH
    cM
    cJ
    cfv
    co
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cH
    wceq
    vj
    cv
    #
    cI
    wceq
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    @4
    @5
    cM
    co
    cif
    cmpt2
    #
    cD
    cfv
    cH
    cI
    cM
    cN
    cR
    cminmar1
    co
    #
    cfv
    co
    #
    cD
    cfv
    cA
    cB
    cD
    cR
    @6
    vi
    cH
    cI
    cJ
    cM
    cN
    @7
    vj
    maducoevalmin1.a
    maducoevalmin1.d
    maducoevalmin1.j
    maducoevalmin1.b
    @6
    eqid
    #
    @7
    eqid
    #
    maducoeval
    @3
    @8
    @10
    cD
    @3
    @10
    @8
    @0
    @2
    @1
    @10
    @8
    wceq
    cA
    cB
    @9
    cR
    @6
    vi
    vj
    cH
    cI
    cM
    cN
    @7
    maducoevalmin1.a
    maducoevalmin1.b
    @9
    eqid
    @11
    @12
    minmar1val
    3com23
    eqcomd
    fveq2d
    eqtrd
end

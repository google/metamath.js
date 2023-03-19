include "crg.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "w3a.mm"
include "cmatrepV.mm"
include "co.mm"
include "cfv.mm"
include "simpll.mm"
include "cur.mm"
include "cmat.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "mat1bas.mm"
include "anim1i.mm"
include "3anass.mm"
include "sylibr.mm"
include "marepvcl.mm"
include "syl2anc.mm"

theorem ma1repvcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let c.1: class .1.
  let cK: class K
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  let cL: class L
  let cM: class M
  assume marepvcl.a: |- A = ( N Mat R )
  assume marepvcl.b: |- B = ( Base ` A )
  assume marepvcl.v: |- V = ( ( Base ` R ) ^m N )
  assume ma1repvcl.1: |- .1. = ( 1r ` A )


  assert |- ( ( ( R e. Ring /\ N e. Fin ) /\ ( C e. V /\ K e. N ) ) -> ( ( .1. ( N matRepV R ) C ) ` K ) e. B )

  proof
    cR
    crg
    wcel
    #
    cN
    cfn
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    #
    cK
    cN
    wcel
    #
    wa
    #
    wa
    #
    @0
    c.1
    cB
    wcel
    #
    @3
    @4
    w3a
    #
    cK
    c.1
    cC
    cN
    cR
    cmatrepV
    co
    co
    cfv
    cB
    wcel
    @0
    @1
    @5
    simpll
    @6
    @7
    @5
    wa
    @8
    @2
    @7
    @5
    cA
    cB
    cR
    c.1
    cN
    marepvcl.a
    marepvcl.b
    c.1
    cA
    cur
    cfv
    cN
    cR
    cmat
    co
    #
    cur
    cfv
    ma1repvcl.1
    cA
    @9
    cur
    marepvcl.a
    fveq2i
    eqtri
    mat1bas
    anim1i
    @7
    @3
    @4
    3anass
    sylibr
    cA
    cB
    cC
    cR
    cK
    c.1
    cN
    cV
    marepvcl.a
    marepvcl.b
    marepvcl.v
    marepvcl
    syl2anc
end

include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "wf1o.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "opex.mm"
include "pm3.2i.mm"
include "cxp.mm"
include "vex.mm"
include "xpsn.mm"
include "eqcomi.mm"
include "mpteq2i.mm"
include "mapsnf1o.mm"
include "mp1i.mm"
include "wceq.mm"
include "a1i.mm"
include "eqidd.mm"
include "simpr.mm"
include "xpsng.mm"
include "sylancom.mm"
include "sneqi.mm"
include "syl6reqr.mm"
include "oveq2d.mm"
include "cfn.mm"
include "snfi.mm"
include "simpl.mm"
include "matbas2.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "f1oeq123d.mm"
include "mpbird.mm"

theorem mat1f1o
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cF: class F
  let cK: class K
  let cO: class O
  let cV: class V
  assume mat1rhmval.k: |- K = ( Base ` R )
  assume mat1rhmval.a: |- A = ( { E } Mat R )
  assume mat1rhmval.b: |- B = ( Base ` A )
  assume mat1rhmval.o: |- O = <. E , E >.
  assume mat1rhmval.f: |- F = ( x e. K |-> { <. O , x >. } )

  disjoint K x
  disjoint O x
  assert |- ( ( R e. Ring /\ E e. V ) -> F : K -1-1-onto-> B )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cK
    cB
    cF
    wf1o
    cK
    cK
    cO
    csn
    #
    cmap
    co
    #
    vx
    cK
    cO
    vx
    cv
    #
    cop
    csn
    #
    cmpt
    #
    wf1o
    #
    cK
    cvv
    wcel
    #
    cO
    cvv
    wcel
    #
    wa
    @8
    @2
    @9
    @10
    cK
    cR
    cbs
    cfv
    cvv
    mat1rhmval.k
    cR
    cbs
    fvex
    eqeltri
    cO
    cE
    cE
    cop
    #
    cvv
    mat1rhmval.o
    cE
    cE
    opex
    eqeltri
    #
    pm3.2i
    vx
    cK
    @7
    cO
    cvv
    cvv
    vx
    cK
    @6
    @3
    @5
    csn
    cxp
    #
    @13
    @6
    cO
    @5
    @12
    vx
    vex
    xpsn
    eqcomi
    mpteq2i
    mapsnf1o
    mp1i
    @2
    cK
    cK
    cB
    @4
    cF
    @7
    cF
    @7
    wceq
    @2
    mat1rhmval.f
    a1i
    @2
    cK
    eqidd
    @2
    @4
    cA
    cbs
    cfv
    #
    cB
    @2
    @4
    cK
    cE
    csn
    #
    @15
    cxp
    #
    cmap
    co
    #
    @14
    @2
    @3
    @16
    cK
    cmap
    @2
    @16
    @11
    csn
    #
    @3
    @0
    @1
    @1
    @16
    @18
    wceq
    @0
    @1
    simpr
    cE
    cE
    cV
    cV
    xpsng
    sylancom
    cO
    @11
    mat1rhmval.o
    sneqi
    syl6reqr
    oveq2d
    @2
    @15
    cfn
    wcel
    @0
    @17
    @14
    wceq
    cE
    snfi
    @0
    @1
    simpl
    cA
    cR
    cK
    @15
    crg
    mat1rhmval.a
    mat1rhmval.k
    matbas2
    sylancr
    eqtrd
    mat1rhmval.b
    syl6reqr
    f1oeq123d
    mpbird
end

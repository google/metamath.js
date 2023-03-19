include "cuhgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "w3a.mm"
include "cs1.mm"
include "cs2.mm"
include "cpths.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "ccycls.mm"
include "cpthson.mm"
include "co.mm"
include "lppthon.mm"
include "pthonispth.mm"
include "syl.mm"
include "cvtx.mm"
include "lpvtx.mm"
include "c1.mm"
include "s2fv1.mm"
include "s1len.mm"
include "fveq2i.mm"
include "a1i.mm"
include "s2fv0.mm"
include "3eqtr4rd.mm"
include "iscycl.mm"
include "sylanbrc.mm"

theorem lp1cycl
  let cA: class A
  let cG: class G
  let cI: class I
  let cJ: class J
  assume lppthon.i: |- I = ( iEdg ` G )


  assert |- ( ( G e. UHGraph /\ J e. dom I /\ ( I ` J ) = { A } ) -> <" J "> ( Cycles ` G ) <" A A "> )

  proof
    cG
    cuhgr
    wcel
    cJ
    cI
    cdm
    wcel
    cJ
    cI
    cfv
    cA
    csn
    wceq
    w3a
    #
    cJ
    cs1
    #
    cA
    cA
    cs2
    #
    cG
    cpths
    cfv
    wbr
    #
    cc0
    @2
    cfv
    #
    @1
    chash
    cfv
    #
    @2
    cfv
    #
    wceq
    #
    @1
    @2
    cG
    ccycls
    cfv
    wbr
    @0
    @1
    @2
    cA
    cA
    cG
    cpthson
    cfv
    co
    wbr
    @3
    cA
    cG
    cI
    cJ
    lppthon.i
    lppthon
    cA
    cA
    @2
    @1
    cG
    pthonispth
    syl
    @0
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    @7
    cA
    cG
    cI
    cJ
    lppthon.i
    lpvtx
    @9
    c1
    @2
    cfv
    #
    cA
    @6
    @4
    cA
    cA
    @8
    s2fv1
    @6
    @10
    wceq
    @9
    @5
    c1
    @2
    cJ
    s1len
    fveq2i
    a1i
    cA
    cA
    @8
    s2fv0
    3eqtr4rd
    syl
    @2
    @1
    cG
    iscycl
    sylanbrc
end

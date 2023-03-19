include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "wi.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "dmeq.mm"
include "ineq2d.mm"
include "reseq2d.mm"
include "reseq2i.mm"
include "syl6eqr.mm"
include "reseq1.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "3anbi2d.mm"
include "ineq1d.mm"
include "eqid.mm"
include "bnj1311.mm"
include "chvarv.mm"

theorem bnj1326
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let cY: class Y
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  assume bnj1326.1: |- B = { d | ( d C_ A /\ A. x e. d _pred ( x , A , R ) C_ d ) }
  assume bnj1326.2: |- Y = <. x , ( f |` _pred ( x , A , R ) ) >.
  assume bnj1326.3: |- C = { f | E. d e. B ( f Fn d /\ A. x e. d ( f ` x ) = ( G ` Y ) ) }
  assume bnj1326.4: |- D = ( dom g i^i dom h )

  disjoint A d
  disjoint A f
  disjoint A x
  disjoint d f
  disjoint d x
  disjoint f x
  disjoint B f
  disjoint G d
  disjoint G f
  disjoint R d
  disjoint R f
  disjoint R x
  disjoint A p
  disjoint A q
  disjoint d p
  disjoint d q
  disjoint f p
  disjoint f q
  disjoint p q
  disjoint p x
  disjoint q x
  disjoint B p
  disjoint B q
  disjoint C p
  disjoint C q
  disjoint D q
  disjoint G p
  disjoint G q
  disjoint R p
  disjoint R q
  disjoint Y p
  disjoint Y q
  disjoint g p
  disjoint g q
  disjoint h q
  assert |- ( ( R _FrSe A /\ g e. C /\ h e. C ) -> ( g |` D ) = ( h |` D ) )

  proof
    cA
    cR
    w-bnj15
    #
    vg
    cv
    #
    cC
    wcel
    #
    vq
    cv
    #
    cC
    wcel
    #
    w3a
    #
    @1
    @1
    cdm
    #
    @3
    cdm
    #
    cin
    #
    cres
    #
    @3
    @8
    cres
    #
    wceq
    #
    wi
    #
    @0
    @2
    vh
    cv
    #
    cC
    wcel
    #
    w3a
    #
    @1
    cD
    cres
    #
    @13
    cD
    cres
    #
    wceq
    #
    wi
    vq
    vh
    @3
    @13
    wceq
    #
    @5
    @15
    @11
    @18
    @19
    @4
    @14
    @0
    @2
    @3
    @13
    cC
    eleq1
    3anbi3d
    @19
    @9
    @16
    @10
    @17
    @19
    @9
    @1
    @6
    @13
    cdm
    #
    cin
    #
    cres
    @16
    @19
    @8
    @21
    @1
    @19
    @7
    @20
    @6
    @3
    @13
    dmeq
    ineq2d
    #
    reseq2d
    cD
    @21
    @1
    bnj1326.4
    reseq2i
    syl6eqr
    @19
    @10
    @13
    @21
    cres
    #
    @17
    @19
    @10
    @3
    @21
    cres
    @23
    @19
    @8
    @21
    @3
    @22
    reseq2d
    @3
    @13
    @21
    reseq1
    eqtrd
    cD
    @21
    @13
    bnj1326.4
    reseq2i
    syl6eqr
    eqeq12d
    imbi12d
    @0
    vp
    cv
    #
    cC
    wcel
    #
    @4
    w3a
    #
    @24
    @24
    cdm
    #
    @7
    cin
    #
    cres
    #
    @3
    @28
    cres
    #
    wceq
    #
    wi
    @12
    vp
    vg
    @24
    @1
    wceq
    #
    @26
    @5
    @31
    @11
    @32
    @25
    @2
    @0
    @4
    @24
    @1
    cC
    eleq1
    3anbi2d
    @32
    @29
    @9
    @30
    @10
    @32
    @29
    @24
    @8
    cres
    @9
    @32
    @28
    @8
    @24
    @32
    @27
    @6
    @7
    @24
    @1
    dmeq
    ineq1d
    #
    reseq2d
    @24
    @1
    @8
    reseq1
    eqtrd
    @32
    @28
    @8
    @3
    @33
    reseq2d
    eqeq12d
    imbi12d
    vx
    cA
    cB
    cC
    @28
    cR
    vf
    vp
    vq
    cG
    cY
    vd
    bnj1326.1
    bnj1326.2
    bnj1326.3
    @28
    eqid
    bnj1311
    chvarv
    chvarv
end

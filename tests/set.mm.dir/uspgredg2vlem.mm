include "wcel.mm"
include "cuspgr.mm"
include "wa.mm"
include "cv.mm"
include "cpr.mm"
include "wceq.mm"
include "crio.mm"
include "eleq2.mm"
include "elrab2.mm"
include "cedg.mm"
include "cfv.mm"
include "w3a.mm"
include "wreu.mm"
include "simpl.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "3jca.mm"
include "cvtx.mm"
include "uspgredg2vtxeu.mm"
include "wb.mm"
include "reueq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "riotacl.mm"
include "3syl.mm"
include "sylan2b.mm"

theorem uspgredg2vlem
  let vz: setvar z
  let cA: class A
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cY: class Y
  assume uspgredg2v.v: |- V = ( Vtx ` G )
  assume uspgredg2v.e: |- E = ( Edg ` G )
  assume uspgredg2v.a: |- A = { e e. E | N e. e }

  disjoint E e
  disjoint G z
  disjoint N e
  disjoint N z
  disjoint V z
  disjoint Y e
  disjoint Y z
  assert |- ( ( G e. USPGraph /\ Y e. A ) -> ( iota_ z e. V Y = { N , z } ) e. V )

  proof
    cY
    cA
    wcel
    cG
    cuspgr
    wcel
    #
    cY
    cE
    wcel
    #
    cN
    cY
    wcel
    #
    wa
    #
    cY
    cN
    vz
    cv
    cpr
    wceq
    #
    vz
    cV
    crio
    cV
    wcel
    #
    cN
    ve
    cv
    #
    wcel
    @2
    ve
    cY
    cE
    cA
    @6
    cY
    cN
    eleq2
    uspgredg2v.a
    elrab2
    @0
    @3
    wa
    #
    @0
    cY
    cG
    cedg
    cfv
    #
    wcel
    #
    @2
    w3a
    #
    @4
    vz
    cV
    wreu
    #
    @5
    @7
    @0
    @9
    @2
    @0
    @3
    simpl
    @1
    @9
    @0
    @2
    @1
    @9
    cE
    @8
    cY
    uspgredg2v.e
    eleq2i
    biimpi
    ad2antrl
    @0
    @1
    @2
    simprr
    3jca
    @10
    @4
    vz
    cG
    cvtx
    cfv
    #
    wreu
    #
    @11
    vz
    cY
    cG
    cN
    uspgredg2vtxeu
    cV
    @12
    wceq
    @11
    @13
    wb
    uspgredg2v.v
    @4
    vz
    cV
    @12
    reueq1
    ax-mp
    sylibr
    @4
    vz
    cV
    riotacl
    3syl
    sylan2b
end

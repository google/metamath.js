include "ccnv.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "wf1o.mm"
include "wfn.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "3syl.mm"
include "wf.mm"
include "f1of.mm"
include "ccom.mm"
include "relco.mm"
include "relbrcnv.mm"
include "cnvco.mm"
include "coeq2i.mm"
include "eqtri.mm"
include "breqi.mm"
include "coass.mm"
include "3bitr3ri.mm"
include "sylib.mm"
include "brcofffn.mm"
include "wrel.mm"
include "wb.mm"
include "f1orel.mm"
include "relbrcnvg.mm"
include "3anbi123d.mm"
include "mpbid.mm"

theorem brco3f1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume brco3f1o.c: |- ( ph -> C : Y -1-1-onto-> Z )
  assume brco3f1o.d: |- ( ph -> D : X -1-1-onto-> Y )
  assume brco3f1o.e: |- ( ph -> E : W -1-1-onto-> X )
  assume brco3f1o.r: |- ( ph -> A ( C o. ( D o. E ) ) B )


  assert |- ( ph -> ( ( `' C ` B ) C B /\ ( `' D ` ( `' C ` B ) ) D ( `' C ` B ) /\ A E ( `' D ` ( `' C ` B ) ) ) )

  proof
    wph
    cB
    cB
    cC
    ccnv
    #
    cfv
    #
    @0
    wbr
    #
    @1
    @1
    cD
    ccnv
    #
    cfv
    #
    @3
    wbr
    #
    @4
    cA
    cE
    ccnv
    #
    wbr
    #
    w3a
    @1
    cB
    cC
    wbr
    #
    @4
    @1
    cD
    wbr
    #
    cA
    @4
    cE
    wbr
    #
    w3a
    wph
    cB
    cA
    @6
    @3
    @0
    cZ
    cY
    cX
    wph
    cW
    cX
    cE
    wf1o
    #
    cX
    cW
    @6
    wf1o
    @6
    cX
    wfn
    brco3f1o.e
    cW
    cX
    cE
    f1ocnv
    cX
    cW
    @6
    f1ofn
    3syl
    wph
    cX
    cY
    cD
    wf1o
    #
    cY
    cX
    @3
    wf1o
    cY
    cX
    @3
    wf
    brco3f1o.d
    cX
    cY
    cD
    f1ocnv
    cY
    cX
    @3
    f1of
    3syl
    wph
    cY
    cZ
    cC
    wf1o
    #
    cZ
    cY
    @0
    wf1o
    cZ
    cY
    @0
    wf
    brco3f1o.c
    cY
    cZ
    cC
    f1ocnv
    cZ
    cY
    @0
    f1of
    3syl
    wph
    cA
    cB
    cC
    cD
    cE
    ccom
    ccom
    #
    wbr
    #
    cB
    cA
    @6
    @3
    @0
    ccom
    #
    ccom
    #
    wbr
    #
    brco3f1o.r
    cB
    cA
    cC
    cD
    ccom
    #
    cE
    ccom
    #
    ccnv
    #
    wbr
    cA
    cB
    @20
    wbr
    @18
    @15
    cB
    cA
    @20
    @19
    cE
    relco
    relbrcnv
    cB
    cA
    @21
    @17
    @21
    @6
    @19
    ccnv
    #
    ccom
    @17
    @19
    cE
    cnvco
    @22
    @16
    @6
    cC
    cD
    cnvco
    coeq2i
    eqtri
    breqi
    cA
    cB
    @20
    @14
    cC
    cD
    cE
    coass
    breqi
    3bitr3ri
    sylib
    brcofffn
    wph
    @2
    @8
    @5
    @9
    @7
    @10
    wph
    @13
    cC
    wrel
    @2
    @8
    wb
    brco3f1o.c
    cY
    cZ
    cC
    f1orel
    cB
    @1
    cC
    relbrcnvg
    3syl
    wph
    @12
    cD
    wrel
    @5
    @9
    wb
    brco3f1o.d
    cX
    cY
    cD
    f1orel
    @1
    @4
    cD
    relbrcnvg
    3syl
    wph
    @11
    cE
    wrel
    @7
    @10
    wb
    brco3f1o.e
    cW
    cX
    cE
    f1orel
    @4
    cA
    cE
    relbrcnvg
    3syl
    3anbi123d
    mpbid
end

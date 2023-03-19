include "ccnv.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
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
include "breqi.mm"
include "bitr3i.mm"
include "sylib.mm"
include "brcoffn.mm"
include "wrel.mm"
include "wb.mm"
include "f1orel.mm"
include "relbrcnvg.mm"
include "anbi12d.mm"
include "mpbid.mm"

theorem brco2f1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume brco2f1o.c: |- ( ph -> C : Y -1-1-onto-> Z )
  assume brco2f1o.d: |- ( ph -> D : X -1-1-onto-> Y )
  assume brco2f1o.r: |- ( ph -> A ( C o. D ) B )


  assert |- ( ph -> ( ( `' C ` B ) C B /\ A D ( `' C ` B ) ) )

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
    cA
    cD
    ccnv
    #
    wbr
    #
    wa
    @1
    cB
    cC
    wbr
    #
    cA
    @1
    cD
    wbr
    #
    wa
    wph
    cB
    cA
    @3
    @0
    cZ
    cY
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
    @3
    cY
    wfn
    brco2f1o.d
    cX
    cY
    cD
    f1ocnv
    cY
    cX
    @3
    f1ofn
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
    brco2f1o.c
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
    ccom
    #
    wbr
    #
    cB
    cA
    @3
    @0
    ccom
    #
    wbr
    #
    brco2f1o.r
    @10
    cB
    cA
    @9
    ccnv
    #
    wbr
    @12
    cB
    cA
    @9
    cC
    cD
    relco
    relbrcnv
    cB
    cA
    @13
    @11
    cC
    cD
    cnvco
    breqi
    bitr3i
    sylib
    brcoffn
    wph
    @2
    @5
    @4
    @6
    wph
    @8
    cC
    wrel
    @2
    @5
    wb
    brco2f1o.c
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
    @7
    cD
    wrel
    @4
    @6
    wb
    brco2f1o.d
    cX
    cY
    cD
    f1orel
    @1
    cA
    cD
    relbrcnvg
    3syl
    anbi12d
    mpbid
end

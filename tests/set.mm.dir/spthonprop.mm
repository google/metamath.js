include "cspths.mm"
include "ctrlson.mm"
include "cspthson.mm"
include "cvv.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wb.mm"
include "3simpc.mm"
include "anim1i.mm"
include "isspthson.mm"
include "syl.mm"
include "df-spthson.mm"
include "cv.mm"
include "cwlks.mm"
include "cpths.mm"
include "spthispth.mm"
include "pthiswlk.mm"
include "adantl.mm"
include "wksonproplem.mm"

theorem spthonprop
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume pthsonfval.v: |- V = ( Vtx ` G )


  assert |- ( F ( A ( SPathsOn ` G ) B ) P -> ( ( G e. _V /\ A e. V /\ B e. V ) /\ ( F e. _V /\ P e. _V ) /\ ( F ( A ( TrailsOn ` G ) B ) P /\ F ( SPaths ` G ) P ) ) )

  proof
    cA
    cB
    cP
    cspths
    vf
    vg
    cF
    cG
    ctrlson
    cV
    cspthson
    vp
    va
    vb
    pthsonfval.v
    cG
    cvv
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    wa
    @1
    @2
    wa
    #
    @4
    wa
    cF
    cP
    cA
    cB
    cG
    cspthson
    cfv
    co
    wbr
    cF
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    co
    wbr
    cF
    cP
    cG
    cspths
    cfv
    #
    wbr
    wa
    wb
    @3
    @5
    @4
    @0
    @1
    @2
    3simpc
    anim1i
    cA
    cB
    cP
    cvv
    cF
    cG
    cV
    cvv
    pthsonfval.v
    isspthson
    syl
    vf
    vg
    vp
    va
    vb
    df-spthson
    vf
    cv
    #
    vp
    cv
    #
    @6
    wbr
    #
    @7
    @8
    cG
    cwlks
    cfv
    wbr
    #
    @3
    @9
    @7
    @8
    cG
    cpths
    cfv
    wbr
    @10
    @8
    @7
    cG
    spthispth
    @8
    @7
    cG
    pthiswlk
    syl
    adantl
    wksonproplem
end

include "cpths.mm"
include "ctrlson.mm"
include "cpthson.mm"
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
include "ispthson.mm"
include "syl.mm"
include "df-pthson.mm"
include "cv.mm"
include "cwlks.mm"
include "pthiswlk.mm"
include "adantl.mm"
include "wksonproplem.mm"

theorem pthsonprop
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


  assert |- ( F ( A ( PathsOn ` G ) B ) P -> ( ( G e. _V /\ A e. V /\ B e. V ) /\ ( F e. _V /\ P e. _V ) /\ ( F ( A ( TrailsOn ` G ) B ) P /\ F ( Paths ` G ) P ) ) )

  proof
    cA
    cB
    cP
    cpths
    vf
    vg
    cF
    cG
    ctrlson
    cV
    cpthson
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
    cpthson
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
    cpths
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
    ispthson
    syl
    vf
    vg
    vp
    va
    vb
    df-pthson
    vf
    cv
    #
    vp
    cv
    #
    @6
    wbr
    @7
    @8
    cG
    cwlks
    cfv
    wbr
    @3
    @8
    @7
    cG
    pthiswlk
    adantl
    wksonproplem
end

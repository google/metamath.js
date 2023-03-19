include "ccycls.mm"
include "cfv.mm"
include "cv.mm"
include "cpths.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "wtru.mm"
include "biidd.mm"
include "cvv.mm"
include "wcel.mm"
include "cwlks.mm"
include "wksv.mm"
include "pthiswlk.mm"
include "ssopab2i.mm"
include "ssexi.mm"
include "a1i.mm"
include "df-cycls.mm"
include "fvmptopab.mm"
include "trud.mm"

theorem cycls
  let vf: setvar f
  let cG: class G
  let vp: setvar p
  let vg: setvar g

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint G g
  disjoint f g
  disjoint g p
  assert |- ( Cycles ` G ) = { <. f , p >. | ( f ( Paths ` G ) p /\ ( p ` 0 ) = ( p ` ( # ` f ) ) ) }

  proof
    cG
    ccycls
    cfv
    vf
    cv
    #
    vp
    cv
    #
    cG
    cpths
    cfv
    wbr
    #
    cc0
    @1
    cfv
    @0
    chash
    cfv
    @1
    cfv
    wceq
    #
    wa
    vf
    vp
    copab
    wceq
    wtru
    @3
    @3
    vf
    vp
    vg
    cpths
    ccycls
    cG
    wtru
    vg
    cv
    cG
    wceq
    wa
    @3
    biidd
    @2
    vf
    vp
    copab
    #
    cvv
    wcel
    wtru
    @4
    @0
    @1
    cG
    cwlks
    cfv
    wbr
    #
    vf
    vp
    copab
    vf
    cG
    vp
    wksv
    @2
    @5
    vf
    vp
    @1
    @0
    cG
    pthiswlk
    ssopab2i
    ssexi
    a1i
    vf
    vg
    vp
    df-cycls
    fvmptopab
    trud
end

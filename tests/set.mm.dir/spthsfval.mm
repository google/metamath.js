include "cspths.mm"
include "cfv.mm"
include "cv.mm"
include "ctrls.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "copab.mm"
include "wceq.mm"
include "wtru.mm"
include "biidd.mm"
include "cvv.mm"
include "wcel.mm"
include "cwlks.mm"
include "wksv.mm"
include "trliswlk.mm"
include "ssopab2i.mm"
include "ssexi.mm"
include "a1i.mm"
include "df-spths.mm"
include "fvmptopab.mm"
include "trud.mm"

theorem spthsfval
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
  assert |- ( SPaths ` G ) = { <. f , p >. | ( f ( Trails ` G ) p /\ Fun `' p ) }

  proof
    cG
    cspths
    cfv
    vf
    cv
    #
    vp
    cv
    #
    cG
    ctrls
    cfv
    wbr
    #
    @1
    ccnv
    wfun
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
    ctrls
    cspths
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
    trliswlk
    ssopab2i
    ssexi
    a1i
    vf
    vg
    vp
    df-spths
    fvmptopab
    trud
end

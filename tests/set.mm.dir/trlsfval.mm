include "ctrls.mm"
include "cfv.mm"
include "cv.mm"
include "cwlks.mm"
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
include "wksv.mm"
include "a1i.mm"
include "df-trls.mm"
include "fvmptopab.mm"
include "trud.mm"

theorem trlsfval
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
  assert |- ( Trails ` G ) = { <. f , p >. | ( f ( Walks ` G ) p /\ Fun `' f ) }

  proof
    cG
    ctrls
    cfv
    vf
    cv
    #
    vp
    cv
    cG
    cwlks
    cfv
    wbr
    #
    @0
    ccnv
    wfun
    #
    wa
    vf
    vp
    copab
    wceq
    wtru
    @2
    @2
    vf
    vp
    vg
    cwlks
    ctrls
    cG
    wtru
    vg
    cv
    cG
    wceq
    wa
    @2
    biidd
    @1
    vf
    vp
    copab
    cvv
    wcel
    wtru
    vf
    cG
    vp
    wksv
    a1i
    vf
    vg
    vp
    df-trls
    fvmptopab
    trud
end

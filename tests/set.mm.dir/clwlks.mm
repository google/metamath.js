include "cclwlks.mm"
include "cfv.mm"
include "cv.mm"
include "cwlks.mm"
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
include "wksv.mm"
include "a1i.mm"
include "df-clwlks.mm"
include "fvmptopab.mm"
include "trud.mm"

theorem clwlks
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
  assert |- ( ClWalks ` G ) = { <. f , p >. | ( f ( Walks ` G ) p /\ ( p ` 0 ) = ( p ` ( # ` f ) ) ) }

  proof
    cG
    cclwlks
    cfv
    vf
    cv
    #
    vp
    cv
    #
    cG
    cwlks
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
    cwlks
    cclwlks
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
    df-clwlks
    fvmptopab
    trud
end

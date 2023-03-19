include "cvtx.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cwlks.mm"
include "wbr.mm"
include "copab.mm"
include "fvex.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "dmex.mm"
include "wrdexg.mm"
include "mp1i.mm"
include "eqid.mm"
include "wlkf.mm"
include "adantl.mm"
include "wlkpwrd.mm"
include "opabex2.mm"
include "ax-mp.mm"

theorem wksv
  let vf: setvar f
  let cG: class G
  let vp: setvar p

  disjoint G f
  disjoint G p
  disjoint f p
  assert |- { <. f , p >. | f ( Walks ` G ) p } e. _V

  proof
    cG
    cvtx
    cfv
    #
    cvv
    wcel
    #
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
    vf
    vp
    copab
    cvv
    wcel
    cG
    cvtx
    fvex
    @1
    @4
    vf
    vp
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    #
    @0
    cword
    #
    cvv
    cvv
    @6
    cvv
    wcel
    @7
    cvv
    wcel
    @1
    @5
    cG
    ciedg
    fvex
    dmex
    @6
    cvv
    wrdexg
    mp1i
    @0
    cvv
    wrdexg
    @4
    @2
    @7
    wcel
    @1
    @3
    @2
    cG
    @5
    @5
    eqid
    wlkf
    adantl
    @4
    @3
    @8
    wcel
    @1
    @3
    @2
    cG
    @0
    @0
    eqid
    wlkpwrd
    adantl
    opabex2
    ax-mp
end

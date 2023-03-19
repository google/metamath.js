include "wfun.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cdm.mm"
include "crn.mm"
include "simp1.mm"
include "cword.mm"
include "wlkf.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "wrdsymbcl.mm"
include "syl2anc.mm"
include "fvelrn.mm"

theorem iedginwlk
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  assume iedginwlk.i: |- I = ( iEdg ` G )


  assert |- ( ( Fun I /\ F ( Walks ` G ) P /\ X e. ( 0 ..^ ( # ` F ) ) ) -> ( I ` ( F ` X ) ) e. ran I )

  proof
    cI
    wfun
    #
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cX
    cc0
    cF
    chash
    cfv
    cfzo
    co
    wcel
    #
    w3a
    #
    @0
    cX
    cF
    cfv
    #
    cI
    cdm
    #
    wcel
    #
    @4
    cI
    cfv
    cI
    crn
    wcel
    @0
    @1
    @2
    simp1
    @3
    cF
    @5
    cword
    wcel
    #
    @2
    @6
    @1
    @0
    @7
    @2
    cP
    cF
    cG
    cI
    iedginwlk.i
    wlkf
    3ad2ant2
    @0
    @1
    @2
    simp3
    cX
    @5
    cF
    wrdsymbcl
    syl2anc
    @4
    cI
    fvelrn
    syl2anc
end

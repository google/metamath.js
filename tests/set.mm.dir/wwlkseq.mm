include "cwwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "cvtx.mm"
include "cword.mm"
include "wceq.mm"
include "chash.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "cvv.mm"
include "eqid.mm"
include "wwlkbp.mm"
include "simprd.mm"
include "eqwrd.mm"
include "syl2an.mm"

theorem wwlkseq
  let cT: class T
  let vi: setvar i
  let cG: class G
  let cW: class W

  disjoint T i
  disjoint W i
  assert |- ( ( W e. ( WWalks ` G ) /\ T e. ( WWalks ` G ) ) -> ( W = T <-> ( ( # ` W ) = ( # ` T ) /\ A. i e. ( 0 ..^ ( # ` W ) ) ( W ` i ) = ( T ` i ) ) ) )

  proof
    cW
    cG
    cwwlks
    cfv
    #
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cT
    @3
    wcel
    #
    cW
    cT
    wceq
    cW
    chash
    cfv
    #
    cT
    chash
    cfv
    wceq
    vi
    cv
    #
    cW
    cfv
    @7
    cT
    cfv
    wceq
    vi
    cc0
    @6
    cfzo
    co
    wral
    wa
    wb
    cT
    @0
    wcel
    #
    @1
    cG
    cvv
    wcel
    #
    @4
    cG
    @2
    cW
    @2
    eqid
    #
    wwlkbp
    simprd
    @8
    @9
    @5
    cG
    @2
    cT
    @10
    wwlkbp
    simprd
    cW
    vi
    @2
    cT
    eqwrd
    syl2an
end

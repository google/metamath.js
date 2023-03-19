include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "erclwwlkeq.mm"
include "wi.mm"
include "fveq2.mm"
include "cvtx.mm"
include "cword.mm"
include "cz.mm"
include "cvv.mm"
include "c0.mm"
include "wne.mm"
include "eqid.mm"
include "clwwlkbp.mm"
include "simp2d.mm"
include "ad2antlr.mm"
include "elfzelz.mm"
include "cshwlen.mm"
include "syl2an.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "com23.mm"
include "3impia.mm"
include "com12.mm"
include "sylbid.mm"

theorem erclwwlkeqlen
  let vw: setvar w
  let vu: setvar u
  let c.sm: class .~
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cW: class W
  let cX: class X
  let cY: class Y
  assume erclwwlk.r: |- .~ = { <. u , w >. | ( u e. ( ClWWalks ` G ) /\ w e. ( ClWWalks ` G ) /\ E. n e. ( 0 ... ( # ` w ) ) u = ( w cyclShift n ) ) }

  disjoint U n
  disjoint U u
  disjoint U w
  disjoint n u
  disjoint n w
  disjoint u w
  disjoint W n
  disjoint W u
  disjoint W w
  disjoint X n
  disjoint Y n
  disjoint G n
  disjoint G u
  disjoint G w
  disjoint n u
  disjoint n w
  disjoint u w
  assert |- ( ( U e. X /\ W e. Y ) -> ( U .~ W -> ( # ` U ) = ( # ` W ) ) )

  proof
    cU
    cX
    wcel
    cW
    cY
    wcel
    wa
    #
    cU
    cW
    c.sm
    wbr
    cU
    cG
    cclwwlk
    cfv
    #
    wcel
    #
    cW
    @1
    wcel
    #
    cU
    cW
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    #
    wrex
    #
    w3a
    #
    cU
    chash
    cfv
    #
    @7
    wceq
    #
    vw
    vu
    c.sm
    cU
    vn
    cG
    cW
    cX
    cY
    erclwwlk.r
    erclwwlkeq
    @10
    @0
    @12
    @2
    @3
    @9
    @0
    @12
    wi
    @2
    @3
    wa
    #
    @0
    @9
    @12
    @13
    @0
    @9
    @12
    wi
    @13
    @0
    wa
    #
    @6
    @12
    vn
    @8
    @14
    @4
    @8
    wcel
    #
    wa
    #
    @6
    @12
    @6
    @16
    @11
    @5
    chash
    cfv
    #
    @7
    cU
    @5
    chash
    fveq2
    @14
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    @4
    cz
    wcel
    @17
    @7
    wceq
    @15
    @3
    @19
    @2
    @0
    @3
    cG
    cvv
    wcel
    @19
    cW
    c0
    wne
    cG
    @18
    cW
    @18
    eqid
    clwwlkbp
    simp2d
    ad2antlr
    @4
    cc0
    @7
    elfzelz
    @4
    @18
    cW
    cshwlen
    syl2an
    sylan9eqr
    ex
    rexlimdva
    ex
    com23
    3impia
    com12
    sylbid
end

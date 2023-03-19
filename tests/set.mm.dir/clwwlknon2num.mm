include "crusgr.mm"
include "wbr.mm"
include "cvtx.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cclwwlknon.mm"
include "co.mm"
include "chash.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cedg.mm"
include "w3a.mm"
include "cword.mm"
include "crab.mm"
include "eqid.mm"
include "clwwlknon2x.mm"
include "a1i.mm"
include "fveq2d.mm"
include "3ancomb.mm"
include "rabbii.mm"
include "fveq2i.mm"
include "rusgrnumwrdl2.mm"
include "syl5eqr.mm"
include "eqtrd.mm"

theorem clwwlknon2num
  let cG: class G
  let cK: class K
  let cX: class X
  let vw: setvar w


  assert |- ( ( G RegUSGraph K /\ X e. ( Vtx ` G ) ) -> ( # ` ( X ( ClWWalksNOn ` G ) 2 ) ) = K )

  proof
    cG
    cK
    crusgr
    wbr
    cX
    cG
    cvtx
    cfv
    #
    wcel
    wa
    #
    cX
    c2
    cG
    cclwwlknon
    cfv
    #
    co
    #
    chash
    cfv
    vw
    cv
    #
    chash
    cfv
    c2
    wceq
    #
    cc0
    @4
    cfv
    #
    c1
    @4
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    #
    @6
    cX
    wceq
    #
    w3a
    #
    vw
    @0
    cword
    #
    crab
    #
    chash
    cfv
    #
    cK
    @1
    @3
    @12
    chash
    @3
    @12
    wceq
    @1
    vw
    @2
    @7
    cG
    @0
    cX
    @2
    eqid
    @0
    eqid
    #
    @7
    eqid
    clwwlknon2x
    a1i
    fveq2d
    @1
    @13
    @5
    @9
    @8
    w3a
    #
    vw
    @11
    crab
    #
    chash
    cfv
    cK
    @16
    @12
    chash
    @15
    @10
    vw
    @11
    @5
    @9
    @8
    3ancomb
    rabbii
    fveq2i
    vw
    cX
    cG
    cK
    @0
    @14
    rusgrnumwrdl2
    syl5eqr
    eqtrd
end

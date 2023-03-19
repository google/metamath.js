include "wcel.mm"
include "cvv.mm"
include "clinds.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "clbs.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "adantr.mm"
include "wss.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "islbs.mm"
include "islinds2.mm"
include "anbi1d.mm"
include "3anan32.mm"
include "syl6rbbr.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem islbs4
  let cB: class B
  let cJ: class J
  let cK: class K
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume islbs4.b: |- B = ( Base ` W )
  assume islbs4.j: |- J = ( LBasis ` W )
  assume islbs4.k: |- K = ( LSpan ` W )


  assert |- ( X e. J <-> ( X e. ( LIndS ` W ) /\ ( K ` X ) = B ) )

  proof
    cX
    cJ
    wcel
    #
    cW
    cvv
    wcel
    #
    cX
    cW
    clinds
    cfv
    wcel
    #
    cX
    cK
    cfv
    cB
    wceq
    #
    wa
    #
    @1
    cX
    cW
    clbs
    cfv
    cJ
    cX
    cW
    clbs
    elfvex
    islbs4.j
    eleq2s
    @2
    @1
    @3
    cX
    cW
    clinds
    elfvex
    adantr
    @1
    @0
    cX
    cB
    wss
    #
    @3
    vk
    cv
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    cX
    @6
    csn
    cdif
    cK
    cfv
    wcel
    wn
    vk
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    @8
    c0g
    cfv
    #
    csn
    cdif
    wral
    vx
    cX
    wral
    #
    w3a
    #
    @4
    vx
    vk
    cX
    @7
    @8
    cJ
    @9
    cK
    cB
    cW
    cvv
    @10
    islbs4.b
    @8
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    islbs4.j
    islbs4.k
    @10
    eqid
    #
    islbs
    @1
    @4
    @5
    @11
    wa
    #
    @3
    wa
    @12
    @1
    @2
    @17
    @3
    vx
    cB
    @8
    @7
    vk
    cX
    cK
    @9
    cW
    cvv
    @10
    islbs4.b
    @14
    islbs4.k
    @13
    @15
    @16
    islinds2
    anbi1d
    @5
    @3
    @11
    3anan32
    syl6rbbr
    bitrd
    pm5.21nii
end

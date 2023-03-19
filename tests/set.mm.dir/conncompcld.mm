include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccld.mm"
include "ccl.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "cuni.mm"
include "ctop.mm"
include "topontop.mm"
include "adantr.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "ssrab2.mm"
include "sspwuni.mm"
include "mpbi.mm"
include "eqsstri.mm"
include "wceq.mm"
include "toponuni.mm"
include "syl5sseq.mm"
include "eqid.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "sscls.mm"
include "conncompid.mm"
include "sseldd.mm"
include "simpl.mm"
include "a1i.mm"
include "conncompconn.mm"
include "clsconn.mm"
include "syl3anc.mm"
include "conncompss.mm"
include "wb.mm"
include "iscld4.mm"
include "mpbird.mm"

theorem conncompcld
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cT: class T
  assume conncomp.2: |- S = U. { x e. ~P X | ( A e. x /\ ( J |`t x ) e. Conn ) }

  disjoint A x
  disjoint J x
  disjoint X x
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B k
  disjoint B x
  disjoint J k
  disjoint J y
  disjoint J z
  disjoint T y
  disjoint X k
  disjoint X y
  disjoint X z
  assert |- ( ( J e. ( TopOn ` X ) /\ A e. X ) -> S e. ( Clsd ` J ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cS
    cJ
    ccld
    cfv
    wcel
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    cS
    wss
    #
    @2
    @4
    cX
    wss
    cA
    @4
    wcel
    cJ
    @4
    crest
    co
    cconn
    wcel
    #
    @5
    @2
    @4
    cJ
    cuni
    #
    cX
    @2
    cJ
    ctop
    wcel
    #
    cS
    @7
    wss
    #
    @4
    @7
    wss
    @0
    @8
    @1
    cX
    cJ
    topontop
    adantr
    #
    @2
    cX
    cS
    @7
    cS
    cA
    vx
    cv
    #
    wcel
    cJ
    @11
    crest
    co
    cconn
    wcel
    wa
    #
    vx
    cX
    cpw
    #
    crab
    #
    cuni
    #
    cX
    conncomp.2
    @14
    @13
    wss
    @15
    cX
    wss
    @12
    vx
    @13
    ssrab2
    @14
    cX
    sspwuni
    mpbi
    eqsstri
    #
    @0
    cX
    @7
    wceq
    @1
    cX
    cJ
    toponuni
    adantr
    #
    syl5sseq
    #
    cS
    cJ
    @7
    @7
    eqid
    #
    clsss3
    syl2anc
    @17
    sseqtr4d
    @2
    cS
    @4
    cA
    @2
    @8
    @9
    cS
    @4
    wss
    @10
    @18
    cS
    cJ
    @7
    @19
    sscls
    syl2anc
    vx
    cA
    cS
    cJ
    cX
    conncomp.2
    conncompid
    sseldd
    @2
    @0
    cS
    cX
    wss
    #
    cJ
    cS
    crest
    co
    cconn
    wcel
    @6
    @0
    @1
    simpl
    @20
    @2
    @16
    a1i
    vx
    cA
    cS
    cJ
    cX
    conncomp.2
    conncompconn
    cS
    cJ
    cX
    clsconn
    syl3anc
    vx
    cA
    cS
    @4
    cJ
    cX
    conncomp.2
    conncompss
    syl3anc
    @2
    @8
    @9
    @3
    @5
    wb
    @10
    @18
    cS
    cJ
    @7
    @19
    iscld4
    syl2anc
    mpbird
end

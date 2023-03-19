include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccld.mm"
include "cin.mm"
include "w3a.mm"
include "cuni.mm"
include "eqid.mm"
include "wss.mm"
include "simp1.mm"
include "inss1.mm"
include "simp2.mm"
include "sseldi.mm"
include "toponss.mm"
include "syl2anc.mm"
include "simp3.mm"
include "sseldd.mm"
include "conncompcld.mm"
include "cldss.mm"
include "syl.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "conncompconn.mm"
include "c0.mm"
include "wne.mm"
include "conncompid.mm"
include "inelcm.mm"
include "inss2.mm"
include "connsubclo.mm"

theorem conncompclo
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let cJ: class J
  let cX: class X
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let cB: class B
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
  assert |- ( ( J e. ( TopOn ` X ) /\ T e. ( J i^i ( Clsd ` J ) ) /\ A e. T ) -> S C_ T )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cT
    cJ
    cJ
    ccld
    cfv
    #
    cin
    #
    wcel
    #
    cA
    cT
    wcel
    #
    w3a
    #
    cS
    cT
    cJ
    cJ
    cuni
    #
    @6
    eqid
    #
    @5
    cS
    @1
    wcel
    #
    cS
    @6
    wss
    @5
    @0
    cA
    cX
    wcel
    #
    @8
    @0
    @3
    @4
    simp1
    #
    @5
    cT
    cX
    cA
    @5
    @0
    cT
    cJ
    wcel
    cT
    cX
    wss
    @10
    @5
    @2
    cJ
    cT
    cJ
    @1
    inss1
    @0
    @3
    @4
    simp2
    #
    sseldi
    #
    cT
    cJ
    cX
    toponss
    syl2anc
    @0
    @3
    @4
    simp3
    #
    sseldd
    #
    vx
    cA
    cS
    cJ
    cX
    conncomp.2
    conncompcld
    syl2anc
    cS
    cJ
    @6
    @7
    cldss
    syl
    @5
    @0
    @9
    cJ
    cS
    crest
    co
    cconn
    wcel
    @10
    @14
    vx
    cA
    cS
    cJ
    cX
    conncomp.2
    conncompconn
    syl2anc
    @12
    @5
    @4
    cA
    cS
    wcel
    #
    cT
    cS
    cin
    c0
    wne
    @13
    @5
    @0
    @9
    @15
    @10
    @14
    vx
    cA
    cS
    cJ
    cX
    conncomp.2
    conncompid
    syl2anc
    cA
    cT
    cS
    inelcm
    syl2anc
    @5
    @2
    @1
    cT
    cJ
    @1
    inss2
    @11
    sseldi
    connsubclo
end

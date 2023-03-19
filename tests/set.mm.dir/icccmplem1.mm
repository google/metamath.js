include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cicc.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cxr.mm"
include "rexrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "eluni2.mm"
include "sylib.mm"
include "wa.mm"
include "csn.mm"
include "snssi.mm"
include "ad2antrl.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "snfi.mm"
include "a1i.mm"
include "elind.mm"
include "wceq.mm"
include "adantr.mm"
include "iccid.mm"
include "syl.mm"
include "ad2antll.mm"
include "eqsstrd.mm"
include "unieq.mm"
include "vex.mm"
include "unisn.mm"
include "syl6eq.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimddv.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "cr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "biimpa.mm"
include "simp3d.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "jca.mm"

theorem icccmplem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cJ: class J
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cC: class C
  let cR: class R
  let cG: class G
  let cV: class V
  assume icccmp.1: |- J = ( topGen ` ran (,) )
  assume icccmp.2: |- T = ( J |`t ( A [,] B ) )
  assume icccmp.3: |- D = ( ( abs o. - ) |` ( RR X. RR ) )
  assume icccmp.4: |- S = { x e. ( A [,] B ) | E. z e. ( ~P U i^i Fin ) ( A [,] x ) C_ U. z }
  assume icccmp.5: |- ( ph -> A e. RR )
  assume icccmp.6: |- ( ph -> B e. RR )
  assume icccmp.7: |- ( ph -> A <_ B )
  assume icccmp.8: |- ( ph -> U C_ J )
  assume icccmp.9: |- ( ph -> ( A [,] B ) C_ U. U )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ph y
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint D x
  disjoint T x
  disjoint T z
  disjoint J z
  disjoint S y
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint R t
  disjoint R v
  disjoint R w
  disjoint R y
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint D w
  disjoint G t
  disjoint G v
  disjoint G w
  disjoint V t
  disjoint V y
  disjoint J u
  disjoint J w
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U w
  assert |- ( ph -> ( A e. S /\ A. y e. S y <_ B ) )

  proof
    wph
    cA
    cS
    wcel
    #
    vy
    cv
    #
    cB
    cle
    wbr
    #
    vy
    cS
    wral
    wph
    cA
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cA
    cA
    cicc
    co
    #
    vz
    cv
    #
    cuni
    #
    wss
    #
    vz
    cU
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @0
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    @4
    wph
    cA
    icccmp.5
    rexrd
    #
    wph
    cB
    icccmp.6
    rexrd
    icccmp.7
    cA
    cB
    lbicc2
    syl3anc
    #
    wph
    cA
    vu
    cv
    #
    wcel
    #
    @11
    vu
    cU
    wph
    cA
    cU
    cuni
    #
    wcel
    @16
    vu
    cU
    wrex
    wph
    @3
    @17
    cA
    icccmp.9
    @14
    sseldd
    vu
    cA
    cU
    eluni2
    sylib
    wph
    @15
    cU
    wcel
    #
    @16
    wa
    #
    wa
    #
    @15
    csn
    #
    @10
    wcel
    @5
    @15
    wss
    #
    @11
    @20
    @9
    cfn
    @21
    @20
    @21
    cU
    wss
    #
    @21
    @9
    wcel
    @18
    @23
    wph
    @16
    @15
    cU
    snssi
    ad2antrl
    @21
    cU
    @15
    snex
    elpw
    sylibr
    @21
    cfn
    wcel
    @20
    @15
    snfi
    a1i
    elind
    @20
    @5
    cA
    csn
    #
    @15
    @20
    @12
    @5
    @24
    wceq
    wph
    @12
    @19
    @13
    adantr
    cA
    iccid
    syl
    @16
    @24
    @15
    wss
    wph
    @18
    cA
    @15
    snssi
    ad2antll
    eqsstrd
    @8
    @22
    vz
    @21
    @10
    @6
    @21
    wceq
    #
    @7
    @15
    @5
    @25
    @7
    @21
    cuni
    @15
    @6
    @21
    unieq
    @15
    vu
    vex
    unisn
    syl6eq
    sseq2d
    rspcev
    syl2anc
    rexlimddv
    cA
    vx
    cv
    #
    cicc
    co
    #
    @7
    wss
    #
    vz
    @10
    wrex
    #
    @11
    vx
    cA
    @3
    cS
    @26
    cA
    wceq
    #
    @28
    @8
    vz
    @10
    @30
    @27
    @5
    @7
    @26
    cA
    cA
    cicc
    oveq2
    sseq1d
    rexbidv
    icccmp.4
    elrab2
    sylanbrc
    wph
    @2
    vy
    cS
    @1
    cS
    wcel
    wph
    @1
    @3
    wcel
    #
    @2
    cS
    @3
    @1
    cS
    @29
    vx
    @3
    crab
    @3
    icccmp.4
    @29
    vx
    @3
    ssrab2
    eqsstri
    sseli
    wph
    @31
    wa
    @1
    cr
    wcel
    #
    cA
    @1
    cle
    wbr
    #
    @2
    wph
    @31
    @32
    @33
    @2
    w3a
    #
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @31
    @34
    wb
    icccmp.5
    icccmp.6
    cA
    cB
    @1
    elicc2
    syl2anc
    biimpa
    simp3d
    sylan2
    ralrimiva
    jca
end

include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cuni.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "syl5ss.mm"
include "icccmplem1.mm"
include "simpld.mm"
include "ne0i.mm"
include "syl.mm"
include "simprd.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "suprub.mm"
include "syl31anc.mm"
include "wb.mm"
include "suprleub.mm"
include "mpbird.mm"
include "w3a.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "sseldd.mm"
include "eluni2.mm"
include "sylib.mm"
include "wa.mm"
include "cbl.mm"
include "cfv.mm"
include "crp.mm"
include "wi.mm"
include "sselda.mm"
include "cxmt.mm"
include "rexmet.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cmopn.mm"
include "eqid.mm"
include "tgioo.mm"
include "eqtri.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "ex.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cif.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "icccmplem2.mm"
include "rexlimdvaa.mm"
include "syld.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem icccmplem3
  let wph: wff ph
  let vx: setvar x
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
  let vy: setvar y
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

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint A x
  disjoint A z
  disjoint D x
  disjoint T x
  disjoint T z
  disjoint J z
  disjoint U x
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
  disjoint x y
  disjoint y z
  disjoint B y
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint R t
  disjoint R v
  disjoint R w
  disjoint R y
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
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
  disjoint S y
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U y
  assert |- ( ph -> B e. S )

  proof
    wph
    cS
    cr
    clt
    csup
    #
    vu
    cv
    #
    wcel
    #
    vu
    cU
    wrex
    #
    cB
    cS
    wcel
    #
    wph
    @0
    cU
    cuni
    #
    wcel
    @3
    wph
    cA
    cB
    cicc
    co
    #
    @5
    @0
    icccmp.9
    wph
    @0
    @6
    wcel
    #
    @0
    cr
    wcel
    #
    cA
    @0
    cle
    wbr
    #
    @0
    cB
    cle
    wbr
    #
    wph
    cS
    cr
    wss
    #
    cS
    c0
    wne
    #
    vy
    cv
    #
    vv
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vv
    cr
    wrex
    #
    @8
    wph
    cS
    @6
    cr
    cS
    cA
    vx
    cv
    cicc
    co
    vz
    cv
    cuni
    wss
    vz
    cU
    cpw
    cfn
    cin
    wrex
    #
    vx
    @6
    crab
    @6
    icccmp.4
    @18
    vx
    @6
    ssrab2
    eqsstri
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @6
    cr
    wss
    icccmp.5
    icccmp.6
    cA
    cB
    iccssre
    syl2anc
    syl5ss
    #
    wph
    cA
    cS
    wcel
    #
    @12
    wph
    @22
    @13
    cB
    cle
    wbr
    #
    vy
    cS
    wral
    #
    wph
    vx
    vy
    vz
    cA
    cB
    cD
    cS
    cT
    cU
    cJ
    icccmp.1
    icccmp.2
    icccmp.3
    icccmp.4
    icccmp.5
    icccmp.6
    icccmp.7
    icccmp.8
    icccmp.9
    icccmplem1
    #
    simpld
    #
    cS
    cA
    ne0i
    syl
    #
    wph
    @20
    @24
    @17
    icccmp.6
    wph
    @22
    @24
    @25
    simprd
    #
    @16
    @24
    vv
    cB
    cr
    @14
    cB
    wceq
    @15
    @23
    vy
    cS
    @14
    cB
    @13
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vv
    vy
    cS
    suprcl
    syl3anc
    wph
    @11
    @12
    @17
    @22
    @9
    @21
    @27
    @29
    @26
    vv
    vy
    cS
    cA
    suprub
    syl31anc
    wph
    @10
    @24
    @28
    wph
    @11
    @12
    @17
    @20
    @10
    @24
    wb
    @21
    @27
    @29
    icccmp.6
    vv
    vy
    vy
    cS
    cB
    suprleub
    syl31anc
    mpbird
    wph
    @19
    @20
    @7
    @8
    @9
    @10
    w3a
    wb
    icccmp.5
    icccmp.6
    cA
    cB
    @0
    elicc2
    syl2anc
    mpbir3and
    sseldd
    vu
    @0
    cU
    eluni2
    sylib
    wph
    @2
    @4
    vu
    cU
    wph
    @1
    cU
    wcel
    #
    wa
    #
    @2
    @0
    vw
    cv
    #
    cD
    cbl
    cfv
    co
    @1
    wss
    #
    vw
    crp
    wrex
    #
    @4
    @31
    @1
    cJ
    wcel
    #
    @2
    @34
    wi
    wph
    cU
    cJ
    @1
    icccmp.8
    sselda
    @35
    @2
    @34
    cD
    cr
    cxmt
    cfv
    wcel
    @35
    @2
    @34
    cD
    icccmp.3
    rexmet
    vw
    @1
    cD
    @0
    cJ
    cr
    cJ
    cioo
    crn
    ctg
    cfv
    cD
    cmopn
    cfv
    #
    icccmp.1
    cD
    @36
    icccmp.3
    @36
    eqid
    tgioo
    eqtri
    mopni2
    mp3an1
    ex
    syl
    @31
    @33
    @4
    vw
    crp
    @31
    @32
    crp
    wcel
    #
    @33
    wa
    #
    wa
    vx
    vz
    cA
    cB
    @32
    cD
    @0
    @32
    c2
    cdiv
    co
    caddc
    co
    #
    cB
    cle
    wbr
    @39
    cB
    cif
    #
    cS
    cT
    cU
    @0
    cJ
    @1
    icccmp.1
    icccmp.2
    icccmp.3
    icccmp.4
    wph
    @19
    @30
    @38
    icccmp.5
    ad2antrr
    wph
    @20
    @30
    @38
    icccmp.6
    ad2antrr
    wph
    cA
    cB
    cle
    wbr
    @30
    @38
    icccmp.7
    ad2antrr
    wph
    cU
    cJ
    wss
    @30
    @38
    icccmp.8
    ad2antrr
    wph
    @6
    @5
    wss
    @30
    @38
    icccmp.9
    ad2antrr
    wph
    @30
    @38
    simplr
    @31
    @37
    @33
    simprl
    @31
    @37
    @33
    simprr
    @0
    eqid
    @40
    eqid
    icccmplem2
    rexlimdvaa
    syld
    rexlimdva
    mpd
end

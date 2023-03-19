include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cin.mm"
include "filsspw.mm"
include "0nelfil.mm"
include "filtop.mm"
include "3jca.mm"
include "elpwi.mm"
include "wa.mm"
include "filss.mm"
include "3exp2.mm"
include "com23.mm"
include "imp.mm"
include "rexlimdv.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "filin.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "cfbas.mm"
include "wne.mm"
include "wnel.mm"
include "simp11.mm"
include "simp13.mm"
include "ne0i.mm"
include "syl.mm"
include "simp12.mm"
include "df-nel.mm"
include "sylibr.mm"
include "ssid.mm"
include "sseq1.mm"
include "rspcev.mm"
include "mpan2.mm"
include "ralimi.mm"
include "3ad2ant3.mm"
include "wb.mm"
include "isfbas2.mm"
include "mpbir2and.mm"
include "wex.mm"
include "n0.mm"
include "elin.mm"
include "anim2i.mm"
include "sylbi.mm"
include "eximi.mm"
include "df-rex.mm"
include "imim1i.mm"
include "3ad2ant2.mm"
include "isfil.mm"
include "sylanbrc.mm"
include "impbii.mm"

theorem isfil2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let vz: setvar z

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint F z
  disjoint x z
  disjoint y z
  disjoint X z
  assert |- ( F e. ( Fil ` X ) <-> ( ( F C_ ~P X /\ -. (/) e. F /\ X e. F ) /\ A. x e. ~P X ( E. y e. F y C_ x -> x e. F ) /\ A. x e. F A. y e. F ( x i^i y ) e. F ) )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cF
    cX
    cpw
    #
    wss
    #
    c0
    cF
    wcel
    wn
    #
    cX
    cF
    wcel
    #
    w3a
    #
    vy
    cv
    #
    vx
    cv
    #
    wss
    #
    vy
    cF
    wrex
    #
    @7
    cF
    wcel
    #
    wi
    #
    vx
    @1
    wral
    #
    @7
    @6
    cin
    #
    cF
    wcel
    #
    vy
    cF
    wral
    #
    vx
    cF
    wral
    #
    w3a
    #
    @0
    @5
    @12
    @16
    @0
    @2
    @3
    @4
    cF
    cX
    filsspw
    cF
    cX
    0nelfil
    cF
    cX
    filtop
    3jca
    @0
    @11
    vx
    @1
    @7
    @1
    wcel
    @0
    @7
    cX
    wss
    #
    @11
    @7
    cX
    elpwi
    @0
    @18
    wa
    @8
    @10
    vy
    cF
    @0
    @18
    @6
    cF
    wcel
    #
    @8
    @10
    wi
    #
    wi
    @0
    @19
    @18
    @20
    @0
    @19
    @18
    @8
    @10
    @6
    @7
    cF
    cX
    filss
    3exp2
    com23
    imp
    rexlimdv
    sylan2
    ralrimiva
    @0
    @14
    vx
    vy
    cF
    cF
    @0
    @10
    @19
    @14
    @7
    @6
    cF
    cX
    filin
    3expb
    ralrimivva
    3jca
    @17
    cF
    cX
    cfbas
    cfv
    wcel
    #
    cF
    @7
    cpw
    #
    cin
    #
    c0
    wne
    #
    @10
    wi
    #
    vx
    @1
    wral
    #
    @0
    @17
    @21
    @2
    cF
    c0
    wne
    #
    c0
    cF
    wnel
    #
    vz
    cv
    #
    @13
    wss
    #
    vz
    cF
    wrex
    #
    vy
    cF
    wral
    #
    vx
    cF
    wral
    #
    w3a
    #
    @2
    @3
    @4
    @12
    @16
    simp11
    @17
    @27
    @28
    @33
    @17
    @4
    @27
    @2
    @3
    @4
    @12
    @16
    simp13
    #
    cF
    cX
    ne0i
    syl
    @17
    @3
    @28
    @2
    @3
    @4
    @12
    @16
    simp12
    c0
    cF
    df-nel
    sylibr
    @16
    @5
    @33
    @12
    @15
    @32
    vx
    cF
    @14
    @31
    vy
    cF
    @14
    @13
    @13
    wss
    #
    @31
    @13
    ssid
    @30
    @36
    vz
    @13
    cF
    @29
    @13
    @13
    sseq1
    rspcev
    mpan2
    ralimi
    ralimi
    3ad2ant3
    3jca
    @17
    @4
    @21
    @2
    @34
    wa
    wb
    @35
    vx
    vy
    vz
    cF
    cX
    cF
    isfbas2
    syl
    mpbir2and
    @12
    @5
    @26
    @16
    @11
    @25
    vx
    @1
    @24
    @9
    @10
    @24
    @19
    @8
    wa
    #
    vy
    wex
    #
    @9
    @24
    @6
    @23
    wcel
    #
    vy
    wex
    @38
    vy
    @23
    n0
    @39
    @37
    vy
    @39
    @19
    @6
    @22
    wcel
    #
    wa
    @37
    @6
    cF
    @22
    elin
    @40
    @8
    @19
    @6
    @7
    elpwi
    anim2i
    sylbi
    eximi
    sylbi
    @8
    vy
    cF
    df-rex
    sylibr
    imim1i
    ralimi
    3ad2ant2
    vx
    cF
    cX
    isfil
    sylanbrc
    impbii
end

include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cv.mm"
include "cin.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "elun1.mm"
include "elun2.mm"
include "anim12i.mm"
include "fbasssin.mm"
include "3expb.mm"
include "sylan2.mm"
include "ralrimivva.mm"
include "cpw.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "w3a.mm"
include "fbsspw.mm"
include "adantr.mm"
include "adantl.mm"
include "unssd.mm"
include "a1d.mm"
include "ssun1.mm"
include "fbasne0.mm"
include "ssn0.mm"
include "sylancr.mm"
include "wn.mm"
include "0nelfb.mm"
include "wo.mm"
include "df-nel.mm"
include "elun.mm"
include "notbii.mm"
include "ioran.mm"
include "3bitri.mm"
include "biimpri.mm"
include "syl2an.mm"
include "wi.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "pm3.2.mm"
include "syl.mm"
include "r19.26.mm"
include "ralun.mm"
include "ralimi.mm"
include "sylbir.mm"
include "syl6.mm"
include "ralcom.mm"
include "weq.mm"
include "ineq1.mm"
include "sseq2d.mm"
include "rexbidv.mm"
include "cbvralv.mm"
include "ralbii.mm"
include "ineq2.mm"
include "incom.mm"
include "syl6eq.mm"
include "cbvral2v.mm"
include "biimpi.mm"
include "ssun2.mm"
include "expcom.mm"
include "jcad.mm"
include "3jcad.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "isfbas2.mm"
include "sylibrd.mm"
include "impbid2.mm"

theorem fbun
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cX: class X
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint F w
  disjoint X w
  assert |- ( ( F e. ( fBas ` X ) /\ G e. ( fBas ` X ) ) -> ( ( F u. G ) e. ( fBas ` X ) <-> A. x e. F A. y e. G E. z e. ( F u. G ) z C_ ( x i^i y ) ) )

  proof
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cF
    cG
    cun
    #
    @0
    wcel
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wss
    #
    vz
    @4
    wrex
    #
    vy
    cG
    wral
    #
    vx
    cF
    wral
    #
    @5
    @11
    vx
    vy
    cF
    cG
    @7
    cF
    wcel
    #
    @8
    cG
    wcel
    #
    wa
    @5
    @7
    @4
    wcel
    #
    @8
    @4
    wcel
    #
    wa
    @11
    @14
    @16
    @15
    @17
    @7
    cF
    cG
    elun1
    @8
    cG
    cF
    elun2
    anim12i
    @5
    @16
    @17
    @11
    vz
    @7
    @8
    @4
    cX
    fbasssin
    3expb
    sylan2
    ralrimivva
    @3
    @13
    @4
    cX
    cpw
    #
    wss
    #
    @4
    c0
    wne
    #
    c0
    @4
    wnel
    #
    @11
    vy
    @4
    wral
    #
    vx
    @4
    wral
    #
    w3a
    #
    wa
    #
    @5
    @3
    @13
    @19
    @24
    @3
    @19
    @13
    @3
    cF
    cG
    @18
    @1
    cF
    @18
    wss
    @2
    cX
    cF
    fbsspw
    adantr
    @2
    cG
    @18
    wss
    @1
    cX
    cG
    fbsspw
    adantl
    unssd
    a1d
    @3
    @13
    @20
    @21
    @23
    @3
    @20
    @13
    @1
    @20
    @2
    @1
    cF
    @4
    wss
    #
    cF
    c0
    wne
    @20
    cF
    cG
    ssun1
    #
    cX
    cF
    fbasne0
    cF
    @4
    ssn0
    sylancr
    adantr
    a1d
    @3
    @21
    @13
    @1
    c0
    cF
    wcel
    #
    wn
    #
    c0
    cG
    wcel
    #
    wn
    #
    @21
    @2
    cX
    cF
    0nelfb
    cX
    cG
    0nelfb
    @21
    @29
    @31
    wa
    #
    @21
    c0
    @4
    wcel
    #
    wn
    @28
    @30
    wo
    #
    wn
    @32
    c0
    @4
    df-nel
    @33
    @34
    c0
    cF
    cG
    elun
    notbii
    @28
    @30
    ioran
    3bitri
    biimpri
    syl2an
    a1d
    @3
    @13
    @22
    vx
    cF
    wral
    #
    @22
    vx
    cG
    wral
    #
    wa
    @23
    @3
    @13
    @35
    @36
    @3
    @13
    @11
    vy
    cF
    wral
    #
    vx
    cF
    wral
    #
    @13
    wa
    #
    @35
    @3
    @38
    @13
    @39
    wi
    @1
    @38
    @2
    @1
    @11
    vx
    vy
    cF
    cF
    @1
    @14
    @8
    cF
    wcel
    #
    @11
    @26
    @1
    @14
    @40
    w3a
    @10
    vz
    cF
    wrex
    @11
    @27
    vz
    @7
    @8
    cF
    cX
    fbasssin
    @10
    vz
    cF
    @4
    ssrexv
    mpsyl
    3expb
    ralrimivva
    adantr
    @38
    @13
    pm3.2
    syl
    @39
    @37
    @12
    wa
    #
    vx
    cF
    wral
    @35
    @37
    @12
    vx
    cF
    r19.26
    @41
    @22
    vx
    cF
    @11
    vy
    cF
    cG
    ralun
    #
    ralimi
    sylbir
    syl6
    @3
    @13
    @37
    vx
    cG
    wral
    #
    @12
    vx
    cG
    wral
    #
    wa
    #
    @36
    @13
    @3
    @45
    @13
    @43
    @3
    @44
    @13
    @43
    @13
    @11
    vx
    cF
    wral
    #
    vy
    cG
    wral
    @6
    vw
    cv
    #
    @8
    cin
    #
    wss
    #
    vz
    @4
    wrex
    #
    vw
    cF
    wral
    #
    vy
    cG
    wral
    @43
    @11
    vx
    vy
    cF
    cG
    ralcom
    @46
    @51
    vy
    cG
    @11
    @50
    vx
    vw
    cF
    vx
    vw
    weq
    #
    @10
    @49
    vz
    @4
    @52
    @9
    @48
    @6
    @7
    @47
    @8
    ineq1
    sseq2d
    rexbidv
    cbvralv
    ralbii
    @50
    @11
    @6
    @47
    @7
    cin
    #
    wss
    #
    vz
    @4
    wrex
    vy
    vw
    vx
    vy
    cG
    cF
    vy
    vx
    weq
    #
    @49
    @54
    vz
    @4
    @55
    @48
    @53
    @6
    @8
    @7
    @47
    ineq2
    sseq2d
    rexbidv
    vw
    vy
    weq
    #
    @54
    @10
    vz
    @4
    @56
    @53
    @9
    @6
    @56
    @53
    @8
    @7
    cin
    @9
    @47
    @8
    @7
    ineq1
    @8
    @7
    incom
    syl6eq
    sseq2d
    rexbidv
    cbvral2v
    3bitri
    biimpi
    @2
    @44
    @1
    @2
    @11
    vx
    vy
    cG
    cG
    @2
    @7
    cG
    wcel
    #
    @15
    @11
    cG
    @4
    wss
    @2
    @57
    @15
    w3a
    @10
    vz
    cG
    wrex
    @11
    cG
    cF
    ssun2
    vz
    @7
    @8
    cG
    cX
    fbasssin
    @10
    vz
    cG
    @4
    ssrexv
    mpsyl
    3expb
    ralrimivva
    adantl
    anim12i
    expcom
    @45
    @41
    vx
    cG
    wral
    @36
    @37
    @12
    vx
    cG
    r19.26
    @41
    @22
    vx
    cG
    @42
    ralimi
    sylbir
    syl6
    jcad
    @22
    vx
    cF
    cG
    ralun
    syl6
    3jcad
    jcad
    @3
    cX
    cfbas
    cdm
    #
    wcel
    #
    @5
    @25
    wb
    @1
    @59
    @2
    cF
    cX
    cfbas
    elfvdm
    adantr
    vx
    vy
    vz
    @58
    cX
    @4
    isfbas2
    syl
    sylibrd
    impbid2
end

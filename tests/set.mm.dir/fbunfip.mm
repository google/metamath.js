include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cun.mm"
include "cfi.mm"
include "wn.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wne.mm"
include "wral.mm"
include "w3o.mm"
include "elfiun.mm"
include "notbid.mm"
include "w3a.mm"
include "3ioran.mm"
include "df-3an.mm"
include "bitr2i.mm"
include "syl6bbr.mm"
include "nesym.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitri.mm"
include "fbasfip.mm"
include "anim12i.mm"
include "biantrurd.mm"
include "syl5rbb.mm"
include "wss.mm"
include "wi.mm"
include "ssfii.mm"
include "ssralv.mm"
include "syl.mm"
include "ralimdv.mm"
include "sylan9.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "ineq2.mm"
include "cbvral2v.mm"
include "fbssfi.mm"
include "r19.29.mm"
include "ss2in.mm"
include "sseq2.mm"
include "ss0.mm"
include "syl6bi.mm"
include "syl5com.mm"
include "necon3d.mm"
include "ex.mm"
include "com13.mm"
include "imp.mm"
include "rexlimivw.mm"
include "impancom.mm"
include "expimpd.mm"
include "com12.mm"
include "syl2an.mm"
include "an4s.mm"
include "ralrimdvva.mm"
include "syl5bi.mm"
include "impbid.mm"
include "3bitrd.mm"

theorem fbunfip
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint F z
  disjoint X w
  disjoint X z
  disjoint Y w
  disjoint Y z
  assert |- ( ( F e. ( fBas ` X ) /\ G e. ( fBas ` Y ) ) -> ( -. (/) e. ( fi ` ( F u. G ) ) <-> A. x e. F A. y e. G ( x i^i y ) =/= (/) ) )

  proof
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    cG
    cY
    cfbas
    cfv
    #
    wcel
    #
    wa
    #
    c0
    cF
    cG
    cun
    cfi
    cfv
    wcel
    #
    wn
    #
    c0
    cF
    cfi
    cfv
    #
    wcel
    #
    wn
    #
    c0
    cG
    cfi
    cfv
    #
    wcel
    #
    wn
    #
    wa
    #
    c0
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    wceq
    #
    vy
    @10
    wrex
    #
    vx
    @7
    wrex
    #
    wn
    #
    wa
    #
    @16
    c0
    wne
    #
    vy
    @10
    wral
    #
    vx
    @7
    wral
    #
    @22
    vy
    cG
    wral
    #
    vx
    cF
    wral
    #
    @4
    @6
    @8
    @11
    @19
    w3o
    #
    wn
    #
    @21
    @4
    @5
    @27
    vx
    vy
    c0
    cF
    cG
    @0
    @2
    elfiun
    notbid
    @28
    @9
    @12
    @20
    w3a
    @21
    @8
    @11
    @19
    3ioran
    @9
    @12
    @20
    df-3an
    bitr2i
    syl6bbr
    @24
    @20
    @4
    @21
    @24
    @18
    wn
    #
    vx
    @7
    wral
    @20
    @23
    @29
    vx
    @7
    @23
    @17
    wn
    #
    vy
    @10
    wral
    @29
    @22
    @30
    vy
    @10
    @16
    c0
    nesym
    ralbii
    @17
    vy
    @10
    ralnex
    bitri
    ralbii
    @18
    vx
    @7
    ralnex
    bitri
    @4
    @13
    @20
    @1
    @9
    @3
    @12
    cF
    cX
    fbasfip
    cG
    cY
    fbasfip
    anim12i
    biantrurd
    syl5rbb
    @4
    @24
    @26
    @1
    @24
    @23
    vx
    cF
    wral
    #
    @3
    @26
    @1
    cF
    @7
    wss
    @24
    @31
    wi
    cF
    @0
    ssfii
    @23
    vx
    cF
    @7
    ssralv
    syl
    @3
    @23
    @25
    vx
    cF
    @3
    cG
    @10
    wss
    @23
    @25
    wi
    cG
    @2
    ssfii
    @22
    vy
    cG
    @10
    ssralv
    syl
    ralimdv
    sylan9
    @26
    vz
    cv
    #
    vw
    cv
    #
    cin
    #
    c0
    wne
    #
    vw
    cG
    wral
    #
    vz
    cF
    wral
    #
    @4
    @24
    @22
    @35
    @32
    @15
    cin
    #
    c0
    wne
    vx
    vy
    vz
    vw
    cF
    cG
    @14
    @32
    wceq
    @16
    @38
    c0
    @14
    @32
    @15
    ineq1
    neeq1d
    @15
    @33
    wceq
    @38
    @34
    c0
    @15
    @33
    @32
    ineq2
    neeq1d
    cbvral2v
    @4
    @37
    @22
    vx
    vy
    @7
    @10
    @1
    @14
    @7
    wcel
    #
    @3
    @15
    @10
    wcel
    #
    @37
    @22
    wi
    #
    @1
    @39
    wa
    @32
    @14
    wss
    #
    vz
    cF
    wrex
    #
    @33
    @15
    wss
    #
    vw
    cG
    wrex
    #
    @41
    @3
    @40
    wa
    vz
    @14
    cF
    cX
    fbssfi
    vw
    @15
    cG
    cY
    fbssfi
    @37
    @43
    @45
    wa
    @22
    @37
    @43
    @45
    @22
    @37
    @43
    wa
    @36
    @42
    wa
    #
    vz
    cF
    wrex
    @45
    @22
    wi
    #
    @36
    @42
    vz
    cF
    r19.29
    @46
    @47
    vz
    cF
    @36
    @45
    @42
    @22
    @36
    @45
    wa
    @35
    @44
    wa
    #
    vw
    cG
    wrex
    @42
    @22
    wi
    #
    @35
    @44
    vw
    cG
    r19.29
    @48
    @49
    vw
    cG
    @35
    @44
    @49
    @42
    @44
    @35
    @22
    @42
    @44
    @35
    @22
    wi
    @42
    @44
    wa
    #
    @16
    c0
    @34
    c0
    @50
    @34
    @16
    wss
    #
    @16
    c0
    wceq
    #
    @34
    c0
    wceq
    #
    @32
    @14
    @33
    @15
    ss2in
    @52
    @51
    @34
    c0
    wss
    @53
    @16
    c0
    @34
    sseq2
    @34
    ss0
    syl6bi
    syl5com
    necon3d
    ex
    com13
    imp
    rexlimivw
    syl
    impancom
    rexlimivw
    syl
    expimpd
    com12
    syl2an
    an4s
    ralrimdvva
    syl5bi
    impbid
    3bitrd
end

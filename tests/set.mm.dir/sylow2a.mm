include "cqs.mm"
include "cpw.mm"
include "cdif.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "csu.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "sylow2alem2.mm"
include "wceq.mm"
include "caddc.mm"
include "cin.mm"
include "c0.mm"
include "inass.mm"
include "disjdif.mm"
include "ineq2i.mm"
include "in0.mm"
include "3eqtri.mm"
include "a1i.mm"
include "cun.mm"
include "inundif.mm"
include "eqcomi.mm"
include "cfn.mm"
include "wcel.mm"
include "pwfi.mm"
include "sylib.mm"
include "cga.mm"
include "wer.mm"
include "gaorber.mm"
include "syl.mm"
include "qsss.mm"
include "ssfid.mm"
include "wa.mm"
include "cn0.mm"
include "adantr.mm"
include "sselda.mm"
include "elpwid.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "fsumsplit.mm"
include "qshash.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "wss.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "cuni.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "elin.mm"
include "cec.mm"
include "wi.mm"
include "eqid.mm"
include "sseq1.mm"
include "selpw.mm"
include "syl6bbr.mm"
include "breq1.mm"
include "imbi12d.mm"
include "simpr.mm"
include "erref.mm"
include "vex.mm"
include "elec.mm"
include "sylibr.mm"
include "ssel.mm"
include "syl5com.mm"
include "sylow2alem1.mm"
include "ensn1.mm"
include "syl6eqbr.mm"
include "ex.mm"
include "syld.mm"
include "ectocld.mm"
include "impr.mm"
include "sylan2b.mm"
include "en1b.mm"
include "fveq2d.mm"
include "cvv.mm"
include "vuniex.mm"
include "hashsng.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "sumeq2dv.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "mulid1d.mm"
include "rabexd.mm"
include "inss2.mm"
include "pwexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "wrel.mm"
include "cpr.mm"
include "wrex.mm"
include "relopabi.mm"
include "relssdmrn.mm"
include "erdm.mm"
include "eqeltrd.mm"
include "errn.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "ecelqsg.mm"
include "eqeltrrd.mm"
include "snelpwi.mm"
include "adantl.mm"
include "elind.mm"
include "eqsstr3d.mm"
include "snss.mm"
include "wb.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "adantrl.mm"
include "unieq.mm"
include "unisn.mm"
include "syl6req.mm"
include "impbid1.mm"
include "en3d.mm"
include "hashen.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "3eqtr4rd.mm"
include "diffi.mm"
include "eldifi.mm"
include "sylan2.mm"
include "fsumcl.mm"
include "subaddd.mm"
include "breqtrrd.mm"

theorem sylow2a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cP: class P
  let c.po: class .(+)
  let c.sm: class .~
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vk: setvar k
  let vn: setvar n
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  assume sylow2a.x: |- X = ( Base ` G )
  assume sylow2a.m: |- ( ph -> .(+) e. ( G GrpAct Y ) )
  assume sylow2a.p: |- ( ph -> P pGrp G )
  assume sylow2a.f: |- ( ph -> X e. Fin )
  assume sylow2a.y: |- ( ph -> Y e. Fin )
  assume sylow2a.z: |- Z = { u e. Y | A. h e. X ( h .(+) u ) = u }
  assume sylow2a.r: |- .~ = { <. x , y >. | ( { x , y } C_ Y /\ E. g e. X ( g .(+) x ) = y ) }

  disjoint .~ h
  disjoint g h
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint h u
  disjoint h x
  disjoint h y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint .(+) g
  disjoint .(+) h
  disjoint .(+) u
  disjoint .(+) x
  disjoint .(+) y
  disjoint X g
  disjoint X h
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint h ph
  disjoint Y g
  disjoint Y h
  disjoint Y u
  disjoint Y x
  disjoint Y y
  disjoint h k
  disjoint h n
  disjoint h w
  disjoint h z
  disjoint k n
  disjoint k w
  disjoint k z
  disjoint .~ k
  disjoint n w
  disjoint n z
  disjoint .~ n
  disjoint w z
  disjoint .~ w
  disjoint .~ z
  disjoint g k
  disjoint g w
  disjoint A g
  disjoint A h
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint u w
  disjoint A u
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint g n
  disjoint g v
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint v x
  disjoint v y
  disjoint G v
  disjoint P n
  disjoint P w
  disjoint P z
  disjoint v w
  disjoint h v
  disjoint k v
  disjoint .(+) k
  disjoint u v
  disjoint .(+) v
  disjoint X k
  disjoint n u
  disjoint X n
  disjoint X v
  disjoint Z k
  disjoint Z w
  disjoint Z z
  disjoint k ph
  disjoint ph w
  disjoint ph z
  disjoint g z
  disjoint Y k
  disjoint u z
  disjoint Y w
  disjoint x z
  disjoint y z
  disjoint Y z
  assert |- ( ph -> P || ( ( # ` Y ) - ( # ` Z ) ) )

  proof
    wph
    cP
    cY
    c.sm
    cqs
    #
    cZ
    cpw
    #
    cdif
    #
    vz
    cv
    #
    chash
    cfv
    #
    vz
    csu
    #
    cY
    chash
    cfv
    #
    cZ
    chash
    cfv
    #
    cmin
    co
    #
    cdvds
    wph
    vx
    vy
    vz
    vu
    cP
    c.po
    c.sm
    vg
    vh
    cG
    cX
    cY
    cZ
    sylow2a.x
    sylow2a.m
    sylow2a.p
    sylow2a.f
    sylow2a.y
    sylow2a.z
    sylow2a.r
    sylow2alem2
    wph
    @8
    @5
    wceq
    @7
    @5
    caddc
    co
    #
    @6
    wceq
    wph
    @0
    @4
    vz
    csu
    @0
    @1
    cin
    #
    @4
    vz
    csu
    #
    @5
    caddc
    co
    @6
    @9
    wph
    @10
    @2
    @4
    @0
    vz
    @10
    @2
    cin
    #
    c0
    wceq
    wph
    @12
    @0
    @1
    @2
    cin
    #
    cin
    @0
    c0
    cin
    c0
    @0
    @1
    @2
    inass
    @13
    c0
    @0
    @1
    @0
    disjdif
    ineq2i
    @0
    in0
    3eqtri
    a1i
    @0
    @10
    @2
    cun
    #
    wceq
    wph
    @14
    @0
    @0
    @1
    inundif
    eqcomi
    a1i
    wph
    cY
    cpw
    #
    @0
    wph
    cY
    cfn
    wcel
    #
    @15
    cfn
    wcel
    sylow2a.y
    cY
    pwfi
    sylib
    wph
    cY
    c.sm
    wph
    c.po
    cG
    cY
    cga
    co
    wcel
    cY
    c.sm
    wer
    #
    sylow2a.m
    vx
    vy
    c.po
    c.sm
    vg
    cG
    cX
    cY
    sylow2a.r
    sylow2a.x
    gaorber
    syl
    #
    qsss
    #
    ssfid
    #
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @4
    @22
    @3
    cfn
    wcel
    @4
    cn0
    wcel
    @22
    cY
    @3
    wph
    @16
    @21
    sylow2a.y
    adantr
    @22
    @3
    cY
    wph
    @0
    @15
    @3
    @19
    sselda
    elpwid
    ssfid
    @3
    hashcl
    syl
    nn0cnd
    #
    fsumsplit
    wph
    vz
    cY
    c.sm
    @18
    sylow2a.y
    qshash
    wph
    @7
    @11
    @5
    caddc
    wph
    @10
    c1
    vz
    csu
    #
    @10
    chash
    cfv
    #
    c1
    cmul
    co
    #
    @11
    @7
    wph
    @10
    cfn
    wcel
    #
    c1
    cc
    wcel
    @24
    @26
    wceq
    wph
    @0
    cfn
    wcel
    #
    @10
    @0
    wss
    @27
    @20
    @0
    @1
    inss1
    @0
    @10
    ssfi
    sylancl
    #
    ax-1cn
    @10
    c1
    vz
    fsumconst
    sylancl
    wph
    @10
    @4
    c1
    vz
    wph
    @3
    @10
    wcel
    #
    wa
    #
    @4
    @3
    cuni
    #
    csn
    #
    chash
    cfv
    #
    c1
    @31
    @3
    @33
    chash
    @31
    @3
    c1o
    cen
    wbr
    #
    @3
    @33
    wceq
    #
    @30
    wph
    @21
    @3
    @1
    wcel
    #
    wa
    @35
    @3
    @0
    @1
    elin
    wph
    @21
    @37
    @35
    vw
    cv
    #
    c.sm
    cec
    #
    cZ
    wss
    #
    @39
    c1o
    cen
    wbr
    #
    wi
    @37
    @35
    wi
    wph
    vw
    @3
    cY
    c.sm
    @0
    @0
    eqid
    @39
    @3
    wceq
    #
    @40
    @37
    @41
    @35
    @42
    @40
    @3
    cZ
    wss
    @37
    @39
    @3
    cZ
    sseq1
    vz
    cZ
    selpw
    syl6bbr
    @39
    @3
    c1o
    cen
    breq1
    imbi12d
    wph
    @38
    cY
    wcel
    #
    wa
    #
    @40
    @38
    cZ
    wcel
    #
    @41
    @44
    @38
    @39
    wcel
    #
    @40
    @45
    @44
    @38
    @38
    c.sm
    wbr
    @46
    @44
    @38
    c.sm
    cY
    wph
    @17
    @43
    @18
    adantr
    wph
    @43
    simpr
    erref
    @38
    @38
    c.sm
    vw
    vex
    #
    @47
    elec
    sylibr
    @39
    cZ
    @38
    ssel
    syl5com
    wph
    @45
    @41
    wi
    @43
    wph
    @45
    @41
    wph
    @45
    wa
    #
    @39
    @38
    csn
    #
    c1o
    cen
    wph
    vx
    vy
    vu
    @38
    cP
    c.po
    c.sm
    vg
    vh
    cG
    cX
    cY
    cZ
    sylow2a.x
    sylow2a.m
    sylow2a.p
    sylow2a.f
    sylow2a.y
    sylow2a.z
    sylow2a.r
    sylow2alem1
    #
    @38
    @47
    ensn1
    syl6eqbr
    ex
    adantr
    syld
    ectocld
    impr
    sylan2b
    @3
    en1b
    sylib
    #
    fveq2d
    @32
    cvv
    wcel
    @34
    c1
    wceq
    vz
    vuniex
    #
    @32
    cvv
    hashsng
    ax-mp
    syl6eq
    sumeq2dv
    wph
    @7
    c1
    cmul
    co
    @7
    @26
    wph
    @7
    wph
    @7
    wph
    cZ
    cfn
    wcel
    #
    @7
    cn0
    wcel
    wph
    @16
    cZ
    cY
    wss
    @53
    sylow2a.y
    cZ
    vh
    cv
    vu
    cv
    #
    c.po
    co
    @54
    wceq
    vh
    cX
    wral
    #
    vu
    cY
    crab
    cY
    sylow2a.z
    @55
    vu
    cY
    ssrab2
    eqsstri
    #
    cY
    cZ
    ssfi
    sylancl
    #
    cZ
    hashcl
    syl
    nn0cnd
    #
    mulid1d
    wph
    @7
    @25
    c1
    cmul
    wph
    @7
    @25
    wceq
    #
    cZ
    @10
    cen
    wbr
    #
    wph
    vw
    vz
    cZ
    @10
    @49
    @32
    wph
    @55
    vu
    cY
    cZ
    cfn
    sylow2a.z
    sylow2a.y
    rabexd
    wph
    @10
    @1
    wss
    @1
    cvv
    wcel
    #
    @10
    cvv
    wcel
    @0
    @1
    inss2
    #
    wph
    @53
    @61
    @57
    cZ
    cfn
    pwexg
    syl
    @10
    @1
    cvv
    ssexg
    sylancr
    wph
    @45
    @49
    @10
    wcel
    @48
    @0
    @1
    @49
    @48
    @39
    @49
    @0
    @50
    @48
    c.sm
    cvv
    wcel
    #
    @43
    @39
    @0
    wcel
    wph
    @63
    @45
    wph
    c.sm
    c.sm
    cdm
    #
    c.sm
    crn
    #
    cxp
    #
    wss
    #
    @66
    cvv
    wcel
    #
    @63
    c.sm
    wrel
    @67
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cY
    wss
    vg
    cv
    @69
    c.po
    co
    @70
    wceq
    vg
    cX
    wrex
    wa
    vx
    vy
    c.sm
    sylow2a.r
    relopabi
    c.sm
    relssdmrn
    ax-mp
    wph
    @64
    cfn
    wcel
    @65
    cfn
    wcel
    @68
    wph
    @64
    cY
    cfn
    wph
    @17
    @64
    cY
    wceq
    @18
    cY
    c.sm
    erdm
    syl
    sylow2a.y
    eqeltrd
    wph
    @65
    cY
    cfn
    wph
    @17
    @65
    cY
    wceq
    @18
    cY
    c.sm
    errn
    syl
    sylow2a.y
    eqeltrd
    @64
    @65
    cfn
    cfn
    xpexg
    syl2anc
    c.sm
    @66
    cvv
    ssexg
    sylancr
    adantr
    @48
    cZ
    cY
    @38
    @56
    wph
    @45
    simpr
    sseldi
    cY
    @38
    c.sm
    cvv
    ecelqsg
    syl2anc
    eqeltrrd
    @45
    @49
    @1
    wcel
    wph
    @38
    cZ
    snelpwi
    adantl
    elind
    ex
    wph
    @30
    @32
    cZ
    wcel
    #
    @31
    @33
    cZ
    wss
    @71
    @31
    @33
    @3
    cZ
    @51
    @31
    @3
    cZ
    @31
    @10
    @1
    @3
    @62
    wph
    @30
    simpr
    sseldi
    elpwid
    eqsstr3d
    @32
    cZ
    @52
    snss
    sylibr
    ex
    wph
    @45
    @30
    wa
    #
    @38
    @32
    wceq
    #
    @3
    @49
    wceq
    #
    wb
    wph
    @72
    wa
    @73
    @74
    wph
    @30
    @73
    @74
    wi
    @45
    @31
    @74
    @73
    @36
    @51
    @73
    @49
    @33
    @3
    @38
    @32
    sneq
    eqeq2d
    syl5ibrcom
    adantrl
    @74
    @32
    @49
    cuni
    @38
    @3
    @49
    unieq
    @38
    @47
    unisn
    syl6req
    impbid1
    ex
    en3d
    wph
    @53
    @27
    @59
    @60
    wb
    @57
    @29
    cZ
    @10
    hashen
    syl2anc
    mpbird
    oveq1d
    eqtr3d
    3eqtr4rd
    oveq1d
    3eqtr4rd
    wph
    @6
    @7
    @5
    wph
    @6
    wph
    @16
    @6
    cn0
    wcel
    sylow2a.y
    cY
    hashcl
    syl
    nn0cnd
    @58
    wph
    @2
    @4
    vz
    wph
    @28
    @2
    cfn
    wcel
    @20
    @0
    @1
    diffi
    syl
    @3
    @2
    wcel
    wph
    @21
    @4
    cc
    wcel
    @3
    @0
    @1
    eldifi
    @23
    sylan2
    fsumcl
    subaddd
    mpbird
    breqtrrd
end

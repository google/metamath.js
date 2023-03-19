include "cqs.mm"
include "cpw.mm"
include "cdif.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "pwfi.mm"
include "sylib.mm"
include "cga.mm"
include "co.mm"
include "wer.mm"
include "gaorber.mm"
include "syl.mm"
include "qsss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "diffi.mm"
include "cprime.mm"
include "cz.mm"
include "cexp.mm"
include "wceq.mm"
include "cn0.mm"
include "wrex.mm"
include "cpgp.mm"
include "wbr.mm"
include "wa.mm"
include "cgrp.mm"
include "wb.mm"
include "gagrp.mm"
include "pgpfi.mm"
include "mpbid.mm"
include "simpld.mm"
include "prmz.mm"
include "eldifi.mm"
include "adantr.mm"
include "sselda.mm"
include "elpwid.mm"
include "sylan2.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "wn.mm"
include "cdvds.mm"
include "eldif.mm"
include "cec.mm"
include "wi.mm"
include "eqid.mm"
include "sseq1.mm"
include "selpw.mm"
include "syl6bbr.mm"
include "notbid.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "wral.mm"
include "cpc.mm"
include "cc0.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "erref.mm"
include "vex.mm"
include "elec.mm"
include "sylibr.mm"
include "ne0i.mm"
include "ecss.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pceq0.mm"
include "oveq2.mm"
include "cuni.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "crab.mm"
include "cmul.mm"
include "ssrab2.mm"
include "sylancl.mm"
include "dvdsmul1.mm"
include "cqg.mm"
include "orbsta2.mm"
include "syl21anc.mm"
include "breqtrrd.mm"
include "simprd.mm"
include "breq2.mm"
include "biimpcd.mm"
include "reximdv.mm"
include "sylc.mm"
include "pcprmpw2.mm"
include "eqcomd.mm"
include "c1.mm"
include "zcnd.mm"
include "exp0d.mm"
include "hash1.mm"
include "syl6eqr.mm"
include "eqeq12d.mm"
include "df1o2.mm"
include "snfi.mm"
include "eqeltri.mm"
include "hashen.mm"
include "bitrd.mm"
include "en1b.mm"
include "syl6bb.mm"
include "cxp.mm"
include "wf.mm"
include "ad2antrr.mm"
include "gaf.mm"
include "simprl.mm"
include "fovrnd.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "gaorb.mm"
include "syl3anbrc.mm"
include "ovex.mm"
include "simprr.mm"
include "eleqtrd.mm"
include "elsn.mm"
include "eqtr4d.mm"
include "expr.mm"
include "ralrimdva.mm"
include "sylbid.mm"
include "syl5.mm"
include "sylbird.mm"
include "id.mm"
include "ralbidv.mm"
include "elrab2.mm"
include "baib.mm"
include "adantl.mm"
include "sylibrd.mm"
include "sylow2alem1.mm"
include "snssd.mm"
include "eqsstrd.mm"
include "ex.mm"
include "syld.mm"
include "con1d.mm"
include "ectocld.mm"
include "impr.mm"
include "sylan2b.mm"
include "fsumdvds.mm"

theorem sylow2alem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let cA: class A
  let vv: setvar v
  assume sylow2a.x: |- X = ( Base ` G )
  assume sylow2a.m: |- ( ph -> .(+) e. ( G GrpAct Y ) )
  assume sylow2a.p: |- ( ph -> P pGrp G )
  assume sylow2a.f: |- ( ph -> X e. Fin )
  assume sylow2a.y: |- ( ph -> Y e. Fin )
  assume sylow2a.z: |- Z = { u e. Y | A. h e. X ( h .(+) u ) = u }
  assume sylow2a.r: |- .~ = { <. x , y >. | ( { x , y } C_ Y /\ E. g e. X ( g .(+) x ) = y ) }

  disjoint h z
  disjoint .~ h
  disjoint .~ z
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
  disjoint P z
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
  disjoint Z z
  disjoint h ph
  disjoint ph z
  disjoint g z
  disjoint Y g
  disjoint Y h
  disjoint u z
  disjoint Y u
  disjoint x z
  disjoint Y x
  disjoint y z
  disjoint Y y
  disjoint Y z
  disjoint h k
  disjoint h n
  disjoint h w
  disjoint k n
  disjoint k w
  disjoint k z
  disjoint .~ k
  disjoint n w
  disjoint n z
  disjoint .~ n
  disjoint w z
  disjoint .~ w
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
  disjoint k ph
  disjoint ph w
  disjoint Y k
  disjoint Y w
  assert |- ( ph -> P || sum_ z e. ( ( Y /. .~ ) \ ~P Z ) ( # ` z ) )

  proof
    wph
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
    cP
    wph
    @0
    cfn
    wcel
    #
    @2
    cfn
    wcel
    wph
    cY
    cpw
    #
    cfn
    wcel
    #
    @0
    @6
    wss
    @5
    wph
    cY
    cfn
    wcel
    #
    @7
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
    #
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
    @6
    @0
    ssfi
    syl2anc
    @0
    @1
    diffi
    syl
    wph
    cP
    cprime
    wcel
    #
    cP
    cz
    wcel
    #
    wph
    @13
    cX
    chash
    cfv
    #
    cP
    vn
    cv
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    wph
    cP
    cG
    cpgp
    wbr
    #
    @13
    @18
    wa
    #
    sylow2a.p
    wph
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    @19
    @20
    wb
    wph
    @9
    @21
    sylow2a.m
    c.po
    cG
    cY
    gagrp
    syl
    sylow2a.f
    cP
    vn
    cG
    cX
    sylow2a.x
    pgpfi
    syl2anc
    mpbid
    #
    simpld
    #
    cP
    prmz
    syl
    #
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @4
    @27
    @3
    cfn
    wcel
    #
    @4
    cn0
    wcel
    @26
    wph
    @3
    @0
    wcel
    #
    @28
    @3
    @0
    @1
    eldifi
    wph
    @29
    wa
    #
    @8
    @3
    cY
    wss
    @28
    wph
    @8
    @29
    sylow2a.y
    adantr
    @30
    @3
    cY
    wph
    @0
    @6
    @3
    @12
    sselda
    elpwid
    cY
    @3
    ssfi
    syl2anc
    sylan2
    @3
    hashcl
    syl
    nn0zd
    @26
    wph
    @29
    @3
    @1
    wcel
    #
    wn
    #
    wa
    cP
    @4
    cdvds
    wbr
    #
    @3
    @0
    @1
    eldif
    wph
    @29
    @32
    @33
    vw
    cv
    #
    c.sm
    cec
    #
    cZ
    wss
    #
    wn
    #
    cP
    @35
    chash
    cfv
    #
    cdvds
    wbr
    #
    wi
    @32
    @33
    wi
    wph
    vw
    @3
    cY
    c.sm
    @0
    @0
    eqid
    @35
    @3
    wceq
    #
    @37
    @32
    @39
    @33
    @40
    @36
    @31
    @40
    @36
    @3
    cZ
    wss
    @31
    @35
    @3
    cZ
    sseq1
    vz
    cZ
    selpw
    syl6bbr
    notbid
    @40
    @38
    @4
    cP
    cdvds
    @35
    @3
    chash
    fveq2
    breq2d
    imbi12d
    wph
    @34
    cY
    wcel
    #
    wa
    #
    @39
    @36
    @42
    @39
    wn
    #
    @34
    cZ
    wcel
    #
    @36
    @42
    @43
    vh
    cv
    #
    @34
    c.po
    co
    #
    @34
    wceq
    #
    vh
    cX
    wral
    #
    @44
    @42
    @43
    cP
    @38
    cpc
    co
    #
    cc0
    wceq
    #
    @48
    @42
    @13
    @38
    cn
    wcel
    #
    @50
    @43
    wb
    wph
    @13
    @41
    @24
    adantr
    #
    @42
    @51
    @35
    c0
    wne
    #
    @42
    @34
    @35
    wcel
    #
    @53
    @42
    @34
    @34
    c.sm
    wbr
    @54
    @42
    @34
    c.sm
    cY
    wph
    @10
    @41
    @11
    adantr
    wph
    @41
    simpr
    #
    erref
    @34
    @34
    c.sm
    vw
    vex
    #
    @56
    elec
    sylibr
    #
    @35
    @34
    ne0i
    syl
    @42
    @35
    cfn
    wcel
    #
    @51
    @53
    wb
    wph
    @58
    @41
    wph
    @8
    @35
    cY
    wss
    @58
    sylow2a.y
    wph
    @34
    c.sm
    cY
    @11
    ecss
    cY
    @35
    ssfi
    syl2anc
    #
    adantr
    #
    @35
    hashnncl
    syl
    mpbird
    #
    cP
    @38
    pceq0
    syl2anc
    @50
    cP
    @49
    cexp
    co
    #
    cP
    cc0
    cexp
    co
    #
    wceq
    #
    @42
    @48
    @49
    cc0
    cP
    cexp
    oveq2
    @42
    @64
    @35
    @35
    cuni
    #
    csn
    #
    wceq
    #
    @48
    @42
    @64
    @35
    c1o
    cen
    wbr
    #
    @67
    @42
    @64
    @38
    c1o
    chash
    cfv
    #
    wceq
    #
    @68
    @42
    @62
    @38
    @63
    @69
    @42
    @38
    @62
    @42
    @38
    @16
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    @38
    @62
    wceq
    #
    @42
    @38
    @15
    cdvds
    wbr
    #
    @18
    @72
    @42
    @38
    @38
    vv
    cv
    @34
    c.po
    co
    @34
    wceq
    #
    vv
    cX
    crab
    #
    chash
    cfv
    #
    cmul
    co
    #
    @15
    cdvds
    wph
    @38
    @78
    cdvds
    wbr
    #
    @41
    wph
    @38
    cz
    wcel
    @77
    cz
    wcel
    @79
    wph
    @38
    wph
    @58
    @38
    cn0
    wcel
    @59
    @35
    hashcl
    syl
    nn0zd
    wph
    @77
    wph
    @76
    cfn
    wcel
    #
    @77
    cn0
    wcel
    wph
    @22
    @76
    cX
    wss
    @80
    sylow2a.f
    @75
    vv
    cX
    ssrab2
    cX
    @76
    ssfi
    sylancl
    @76
    hashcl
    syl
    nn0zd
    @38
    @77
    dvdsmul1
    syl2anc
    adantr
    @42
    @9
    @41
    @22
    @15
    @78
    wceq
    wph
    @9
    @41
    sylow2a.m
    adantr
    @55
    wph
    @22
    @41
    sylow2a.f
    adantr
    vx
    vy
    vv
    @34
    c.po
    cG
    @76
    cqg
    co
    #
    vg
    cG
    @76
    c.sm
    cX
    cY
    sylow2a.x
    @76
    eqid
    @81
    eqid
    sylow2a.r
    orbsta2
    syl21anc
    breqtrrd
    wph
    @18
    @41
    wph
    @13
    @18
    @23
    simprd
    adantr
    @74
    @17
    @71
    vn
    cn0
    @17
    @74
    @71
    @15
    @16
    @38
    cdvds
    breq2
    biimpcd
    reximdv
    sylc
    @42
    @13
    @51
    @72
    @73
    wb
    @52
    @61
    @38
    cP
    vn
    pcprmpw2
    syl2anc
    mpbid
    eqcomd
    @42
    @63
    c1
    @69
    @42
    cP
    @42
    cP
    wph
    @14
    @41
    @25
    adantr
    zcnd
    exp0d
    hash1
    syl6eqr
    eqeq12d
    @42
    @58
    c1o
    cfn
    wcel
    @70
    @68
    wb
    @60
    c1o
    c0
    csn
    cfn
    df1o2
    c0
    snfi
    eqeltri
    @35
    c1o
    hashen
    sylancl
    bitrd
    @35
    en1b
    syl6bb
    @42
    @67
    @47
    vh
    cX
    @42
    @45
    cX
    wcel
    #
    @67
    @47
    @42
    @82
    @67
    wa
    #
    wa
    #
    @46
    @65
    @34
    @84
    @46
    @66
    wcel
    @46
    @65
    wceq
    @84
    @46
    @35
    @66
    @84
    @34
    @46
    c.sm
    wbr
    #
    @46
    @35
    wcel
    @84
    @41
    @46
    cY
    wcel
    vk
    cv
    #
    @34
    c.po
    co
    #
    @46
    wceq
    #
    vk
    cX
    wrex
    #
    @85
    @42
    @41
    @83
    @55
    adantr
    #
    @84
    @45
    @34
    cY
    cX
    cY
    c.po
    @84
    @9
    cX
    cY
    cxp
    cY
    c.po
    wf
    wph
    @9
    @41
    @83
    sylow2a.m
    ad2antrr
    c.po
    cG
    cX
    cY
    sylow2a.x
    gaf
    syl
    @42
    @82
    @67
    simprl
    #
    @90
    fovrnd
    @84
    @82
    @46
    @46
    wceq
    #
    @89
    @91
    @46
    eqid
    @88
    @92
    vk
    @45
    cX
    vk
    vh
    weq
    @87
    @46
    @46
    @86
    @45
    @34
    c.po
    oveq1
    eqeq1d
    rspcev
    sylancl
    vx
    vy
    @34
    @46
    c.po
    c.sm
    vg
    vk
    cX
    cY
    sylow2a.r
    gaorb
    syl3anbrc
    @46
    @34
    c.sm
    @45
    @34
    c.po
    ovex
    #
    @56
    elec
    sylibr
    @42
    @82
    @67
    simprr
    #
    eleqtrd
    @46
    @65
    @93
    elsn
    sylib
    @84
    @34
    @66
    wcel
    @34
    @65
    wceq
    @84
    @34
    @35
    @66
    @42
    @54
    @83
    @57
    adantr
    @94
    eleqtrd
    @34
    @65
    @56
    elsn
    sylib
    eqtr4d
    expr
    ralrimdva
    sylbid
    syl5
    sylbird
    @41
    @44
    @48
    wb
    wph
    @44
    @41
    @48
    @45
    vu
    cv
    #
    c.po
    co
    #
    @95
    wceq
    #
    vh
    cX
    wral
    @48
    vu
    @34
    cY
    cZ
    vu
    vw
    weq
    #
    @97
    @47
    vh
    cX
    @98
    @96
    @46
    @95
    @34
    @95
    @34
    @45
    c.po
    oveq2
    @98
    id
    eqeq12d
    ralbidv
    sylow2a.z
    elrab2
    baib
    adantl
    sylibrd
    wph
    @44
    @36
    wi
    @41
    wph
    @44
    @36
    wph
    @44
    wa
    #
    @35
    @34
    csn
    cZ
    wph
    vx
    vy
    vu
    @34
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
    @99
    @34
    cZ
    wph
    @44
    simpr
    snssd
    eqsstrd
    ex
    adantr
    syld
    con1d
    ectocld
    impr
    sylan2b
    fsumdvds
end

include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cpc.mm"
include "co.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "cqs.mm"
include "wrex.mm"
include "cec.mm"
include "wn.mm"
include "wral.mm"
include "c1.mm"
include "caddc.mm"
include "cexp.mm"
include "csu.mm"
include "cdvds.mm"
include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wceq.mm"
include "sylow1lem1.mm"
include "simpld.mm"
include "pcndvds.mm"
include "syl2anc.mm"
include "simprd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "cga.mm"
include "wer.mm"
include "sylow1lem2.mm"
include "gaorber.mm"
include "syl.mm"
include "cpw.mm"
include "cfn.mm"
include "wss.mm"
include "pwfi.mm"
include "sylib.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "sylancl.mm"
include "qshash.mm"
include "breq12d.mm"
include "mtbid.mm"
include "wa.mm"
include "qsss.mm"
include "adantr.mm"
include "cz.mm"
include "prmnn.mm"
include "cn0.mm"
include "pccld.mm"
include "eqeltrrd.mm"
include "peano2nn0.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "erdm.mm"
include "elqsn0.mm"
include "sylan.mm"
include "wb.mm"
include "sselda.mm"
include "elpwid.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "adantlr.mm"
include "clt.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "notbid.mm"
include "rspccva.mm"
include "adantll.mm"
include "cgrp.mm"
include "grpbn0.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "ad2antrr.mm"
include "zred.mm"
include "ltnled.mm"
include "zltp1le.mm"
include "mpbid.mm"
include "pcdvdsb.mm"
include "syl3anc.mm"
include "fsumdvds.mm"
include "mtand.mm"
include "dfrex2.mm"
include "sylibr.mm"
include "wi.mm"
include "eqid.mm"
include "imbi1d.mm"
include "eceq1.mm"
include "fveq2d.mm"
include "rspcev.mm"
include "ex.mm"
include "adantl.mm"
include "ectocld.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem sylow1lem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let c.sm: class .~
  let cS: class S
  let vg: setvar g
  let cG: class G
  let cN: class N
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let cB: class B
  let vh: setvar h
  let cH: class H
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vv: setvar v
  assume sylow1.x: |- X = ( Base ` G )
  assume sylow1.g: |- ( ph -> G e. Grp )
  assume sylow1.f: |- ( ph -> X e. Fin )
  assume sylow1.p: |- ( ph -> P e. Prime )
  assume sylow1.n: |- ( ph -> N e. NN0 )
  assume sylow1.d: |- ( ph -> ( P ^ N ) || ( # ` X ) )
  assume sylow1lem.a: |- .+ = ( +g ` G )
  assume sylow1lem.s: |- S = { s e. ~P X | ( # ` s ) = ( P ^ N ) }
  assume sylow1lem.m: |- .(+) = ( x e. X , y e. S |-> ran ( z e. y |-> ( x .+ z ) ) )
  assume sylow1lem3.1: |- .~ = { <. x , y >. | ( { x , y } C_ S /\ E. g e. X ( g .(+) x ) = y ) }

  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint g w
  disjoint S g
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint N g
  disjoint s w
  disjoint N s
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint X g
  disjoint X s
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint .+ s
  disjoint .+ w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .~ w
  disjoint .~ z
  disjoint .(+) g
  disjoint .(+) w
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint G g
  disjoint G s
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint P g
  disjoint P s
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint a b
  disjoint a c
  disjoint a g
  disjoint a s
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint B a
  disjoint b c
  disjoint b g
  disjoint b s
  disjoint b u
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint c g
  disjoint c s
  disjoint c u
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint g u
  disjoint B g
  disjoint s u
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint a h
  disjoint H a
  disjoint b h
  disjoint H b
  disjoint c h
  disjoint H c
  disjoint g h
  disjoint H g
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint a w
  disjoint S a
  disjoint b w
  disjoint S b
  disjoint c w
  disjoint S c
  disjoint u w
  disjoint S u
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a v
  disjoint N a
  disjoint b k
  disjoint b n
  disjoint b t
  disjoint b v
  disjoint N b
  disjoint g k
  disjoint g n
  disjoint g t
  disjoint g v
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h z
  disjoint N h
  disjoint k n
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint N n
  disjoint s t
  disjoint s v
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint N t
  disjoint u v
  disjoint N u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint N v
  disjoint X a
  disjoint X b
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint X c
  disjoint X h
  disjoint X k
  disjoint X n
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint .+ b
  disjoint .+ c
  disjoint .+ u
  disjoint .+ v
  disjoint .~ a
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) c
  disjoint .(+) u
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint P a
  disjoint P b
  disjoint P h
  disjoint P k
  disjoint P n
  disjoint P t
  disjoint P u
  disjoint P v
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint n ph
  disjoint ph t
  disjoint ph u
  assert |- ( ph -> E. w e. S ( P pCnt ( # ` [ w ] .~ ) ) <_ ( ( P pCnt ( # ` X ) ) - N ) )

  proof
    wph
    cP
    va
    cv
    #
    chash
    cfv
    #
    cpc
    co
    #
    cP
    cX
    chash
    cfv
    #
    cpc
    co
    #
    cN
    cmin
    co
    #
    cle
    wbr
    #
    va
    cS
    c.sm
    cqs
    #
    wrex
    #
    cP
    vw
    cv
    #
    c.sm
    cec
    #
    chash
    cfv
    #
    cpc
    co
    #
    @5
    cle
    wbr
    #
    vw
    cS
    wrex
    #
    wph
    @6
    wn
    #
    va
    @7
    wral
    #
    wn
    @8
    wph
    @16
    cP
    @5
    c1
    caddc
    co
    #
    cexp
    co
    #
    @7
    vz
    cv
    #
    chash
    cfv
    #
    vz
    csu
    #
    cdvds
    wbr
    #
    wph
    cP
    cP
    cS
    chash
    cfv
    #
    cpc
    co
    #
    c1
    caddc
    co
    #
    cexp
    co
    #
    @23
    cdvds
    wbr
    #
    @22
    wph
    cP
    cprime
    wcel
    #
    @23
    cn
    wcel
    #
    @27
    wn
    sylow1.p
    wph
    @29
    @24
    @5
    wceq
    #
    wph
    cP
    c.pl
    cS
    cG
    cN
    cX
    vs
    sylow1.x
    sylow1.g
    sylow1.f
    sylow1.p
    sylow1.n
    sylow1.d
    sylow1lem.a
    sylow1lem.s
    sylow1lem1
    #
    simpld
    #
    cP
    @23
    pcndvds
    syl2anc
    wph
    @26
    @18
    @23
    @21
    cdvds
    wph
    @25
    @17
    cP
    cexp
    wph
    @24
    @5
    c1
    caddc
    wph
    @29
    @30
    @31
    simprd
    #
    oveq1d
    oveq2d
    wph
    vz
    cS
    c.sm
    wph
    c.po
    cG
    cS
    cga
    co
    wcel
    cS
    c.sm
    wer
    #
    wph
    vx
    vy
    vz
    cP
    c.pl
    c.po
    cS
    cG
    cN
    cX
    vs
    sylow1.x
    sylow1.g
    sylow1.f
    sylow1.p
    sylow1.n
    sylow1.d
    sylow1lem.a
    sylow1lem.s
    sylow1lem.m
    sylow1lem2
    vx
    vy
    c.po
    c.sm
    vg
    cG
    cX
    cS
    sylow1lem3.1
    sylow1.x
    gaorber
    syl
    #
    wph
    cX
    cpw
    #
    cfn
    wcel
    #
    cS
    @36
    wss
    cS
    cfn
    wcel
    #
    wph
    cX
    cfn
    wcel
    #
    @37
    sylow1.f
    cX
    pwfi
    sylib
    cS
    vs
    cv
    chash
    cfv
    cP
    cN
    cexp
    co
    wceq
    #
    vs
    @36
    crab
    @36
    sylow1lem.s
    @40
    vs
    @36
    ssrab2
    eqsstri
    @36
    cS
    ssfi
    sylancl
    #
    qshash
    breq12d
    mtbid
    wph
    @16
    wa
    #
    @7
    @20
    vz
    @18
    wph
    @7
    cfn
    wcel
    #
    @16
    wph
    cS
    cpw
    #
    cfn
    wcel
    #
    @7
    @44
    wss
    @43
    wph
    @38
    @45
    @41
    cS
    pwfi
    sylib
    wph
    cS
    c.sm
    @35
    qsss
    #
    @44
    @7
    ssfi
    syl2anc
    adantr
    wph
    @18
    cz
    wcel
    @16
    wph
    @18
    wph
    cP
    @17
    wph
    @28
    cP
    cn
    wcel
    sylow1.p
    cP
    prmnn
    syl
    wph
    @5
    cn0
    wcel
    @17
    cn0
    wcel
    #
    wph
    @24
    @5
    cn0
    @33
    wph
    cP
    @23
    sylow1.p
    @32
    pccld
    eqeltrrd
    @5
    peano2nn0
    syl
    #
    nnexpcld
    nnzd
    adantr
    @42
    @19
    @7
    wcel
    #
    wa
    #
    @20
    wph
    @49
    @20
    cn
    wcel
    #
    @16
    wph
    @49
    wa
    #
    @51
    @19
    c0
    wne
    #
    wph
    c.sm
    cdm
    cS
    wceq
    #
    @49
    @53
    wph
    @34
    @54
    @35
    cS
    c.sm
    erdm
    syl
    cS
    @19
    c.sm
    elqsn0
    sylan
    @52
    @19
    cfn
    wcel
    #
    @51
    @53
    wb
    @52
    @38
    @19
    cS
    wss
    @55
    wph
    @38
    @49
    @41
    adantr
    @52
    @19
    cS
    wph
    @7
    @44
    @19
    @46
    sselda
    elpwid
    cS
    @19
    ssfi
    syl2anc
    @19
    hashnncl
    syl
    mpbird
    adantlr
    #
    nnzd
    #
    @50
    @17
    cP
    @20
    cpc
    co
    #
    cle
    wbr
    #
    @18
    @20
    cdvds
    wbr
    #
    @50
    @5
    @58
    clt
    wbr
    #
    @59
    @50
    @61
    @58
    @5
    cle
    wbr
    #
    wn
    #
    @16
    @49
    @63
    wph
    @15
    @63
    va
    @19
    @7
    va
    vz
    weq
    #
    @6
    @62
    @64
    @2
    @58
    @5
    cle
    @64
    @1
    @20
    cP
    cpc
    @0
    @19
    chash
    fveq2
    oveq2d
    breq1d
    notbid
    rspccva
    adantll
    @50
    @5
    @58
    @50
    @5
    wph
    @5
    cz
    wcel
    #
    @16
    @49
    wph
    @4
    cN
    wph
    @4
    wph
    cP
    @3
    sylow1.p
    wph
    @3
    cn
    wcel
    #
    cX
    c0
    wne
    #
    wph
    cG
    cgrp
    wcel
    @67
    sylow1.g
    cX
    cG
    sylow1.x
    grpbn0
    syl
    wph
    @39
    @66
    @67
    wb
    sylow1.f
    cX
    hashnncl
    syl
    mpbird
    pccld
    nn0zd
    wph
    cN
    sylow1.n
    nn0zd
    zsubcld
    ad2antrr
    #
    zred
    @50
    @58
    @50
    @58
    @50
    cP
    @20
    wph
    @28
    @16
    @49
    sylow1.p
    ad2antrr
    #
    @56
    pccld
    nn0zd
    #
    zred
    ltnled
    mpbird
    @50
    @65
    @58
    cz
    wcel
    @61
    @59
    wb
    @68
    @70
    @5
    @58
    zltp1le
    syl2anc
    mpbid
    @50
    @28
    @20
    cz
    wcel
    @47
    @59
    @60
    wb
    @69
    @57
    wph
    @47
    @16
    @49
    @48
    ad2antrr
    @17
    cP
    @20
    pcdvdsb
    syl3anc
    mpbid
    fsumdvds
    mtand
    @6
    va
    @7
    dfrex2
    sylibr
    wph
    @6
    @14
    va
    @7
    cP
    @19
    c.sm
    cec
    #
    chash
    cfv
    #
    cpc
    co
    #
    @5
    cle
    wbr
    #
    @14
    wi
    #
    @6
    @14
    wi
    wph
    vz
    @0
    cS
    c.sm
    @7
    @7
    eqid
    @71
    @0
    wceq
    #
    @74
    @6
    @14
    @76
    @73
    @2
    @5
    cle
    @76
    @72
    @1
    cP
    cpc
    @71
    @0
    chash
    fveq2
    oveq2d
    breq1d
    imbi1d
    @19
    cS
    wcel
    #
    @75
    wph
    @77
    @74
    @14
    @13
    @74
    vw
    @19
    cS
    vw
    vz
    weq
    #
    @12
    @73
    @5
    cle
    @78
    @11
    @72
    cP
    cpc
    @78
    @10
    @71
    chash
    @9
    @19
    c.sm
    eceq1
    fveq2d
    oveq2d
    breq1d
    rspcev
    ex
    adantl
    ectocld
    rexlimdva
    mpd
end

include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "chash.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "cga.mm"
include "sylow1lem2.mm"
include "gastacl.mm"
include "syl2anc.mm"
include "cle.mm"
include "wbr.mm"
include "sylow1lem4.mm"
include "cdvds.mm"
include "cpc.mm"
include "cec.mm"
include "caddc.mm"
include "cmin.mm"
include "cr.mm"
include "wb.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "wer.mm"
include "gaorber.mm"
include "syl.mm"
include "erdm.mm"
include "eleqtrrd.mm"
include "ecdmn0.mm"
include "sylib.mm"
include "cfn.mm"
include "wss.mm"
include "cpw.mm"
include "pwfi.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "sylancl.mm"
include "ecss.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pccld.mm"
include "nn0red.mm"
include "cgrp.mm"
include "grpbn0.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "cmul.mm"
include "cqg.mm"
include "eqid.mm"
include "orbsta2.mm"
include "syl21anc.mm"
include "oveq2d.mm"
include "cprime.mm"
include "cz.mm"
include "cc0.mm"
include "nnzd.mm"
include "nnne0d.mm"
include "c0g.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "pcmul.mm"
include "syl122anc.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "leadd2d.mm"
include "cn0.mm"
include "pcdvdsb.mm"
include "mpbid.mm"
include "wi.mm"
include "prmnn.mm"
include "nnexpcld.mm"
include "dvdsle.mm"
include "mpd.mm"
include "hashcl.mm"
include "nnred.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"

theorem sylow1lem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let c.sm: class .~
  let cS: class S
  let vg: setvar g
  let vh: setvar h
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vw: setvar w
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
  assume sylow1lem4.b: |- ( ph -> B e. S )
  assume sylow1lem4.h: |- H = { u e. X | ( u .(+) B ) = B }
  assume sylow1lem5.l: |- ( ph -> ( P pCnt ( # ` [ B ] .~ ) ) <_ ( ( P pCnt ( # ` X ) ) - N ) )

  disjoint g s
  disjoint g u
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint s u
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint g h
  disjoint H g
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint S g
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint N g
  disjoint h s
  disjoint h u
  disjoint h z
  disjoint N h
  disjoint N s
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint X g
  disjoint X h
  disjoint X s
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint .+ s
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .~ z
  disjoint .(+) g
  disjoint .(+) u
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint G g
  disjoint G h
  disjoint G s
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint P g
  disjoint P h
  disjoint P s
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint ph u
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
  disjoint a h
  disjoint H a
  disjoint b h
  disjoint H b
  disjoint c h
  disjoint H c
  disjoint a w
  disjoint S a
  disjoint b w
  disjoint S b
  disjoint c w
  disjoint S c
  disjoint g w
  disjoint u w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint S w
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
  disjoint h t
  disjoint h v
  disjoint h w
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
  disjoint s w
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint N t
  disjoint u v
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint N v
  disjoint N w
  disjoint X a
  disjoint X b
  disjoint c k
  disjoint c n
  disjoint c t
  disjoint c v
  disjoint X c
  disjoint X k
  disjoint X n
  disjoint X t
  disjoint X v
  disjoint X w
  disjoint .+ b
  disjoint .+ c
  disjoint .+ v
  disjoint .+ w
  disjoint .~ a
  disjoint .~ w
  disjoint .(+) a
  disjoint .(+) b
  disjoint .(+) c
  disjoint .(+) w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G k
  disjoint G t
  disjoint G v
  disjoint P a
  disjoint P b
  disjoint P k
  disjoint P n
  disjoint P t
  disjoint P v
  disjoint P w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint n ph
  disjoint ph t
  assert |- ( ph -> E. h e. ( SubGrp ` G ) ( # ` h ) = ( P ^ N ) )

  proof
    wph
    cH
    cG
    csubg
    cfv
    #
    wcel
    #
    cH
    chash
    cfv
    #
    cP
    cN
    cexp
    co
    #
    wceq
    #
    vh
    cv
    #
    chash
    cfv
    #
    @3
    wceq
    #
    vh
    @0
    wrex
    wph
    c.po
    cG
    cS
    cga
    co
    wcel
    #
    cB
    cS
    wcel
    #
    @1
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
    #
    sylow1lem4.b
    vu
    cB
    c.po
    cG
    cH
    cX
    cS
    sylow1.x
    sylow1lem4.h
    gastacl
    syl2anc
    #
    wph
    @4
    @2
    @3
    cle
    wbr
    @3
    @2
    cle
    wbr
    #
    wph
    vx
    vy
    vz
    vu
    cB
    cP
    c.pl
    c.po
    c.sm
    cS
    vg
    cG
    cH
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
    sylow1lem3.1
    sylow1lem4.b
    sylow1lem4.h
    sylow1lem4
    wph
    @3
    @2
    cdvds
    wbr
    #
    @12
    wph
    cN
    cP
    @2
    cpc
    co
    #
    cle
    wbr
    #
    @13
    wph
    @15
    cP
    cB
    c.sm
    cec
    #
    chash
    cfv
    #
    cpc
    co
    #
    cN
    caddc
    co
    #
    @18
    @14
    caddc
    co
    #
    cle
    wbr
    wph
    @19
    cP
    cX
    chash
    cfv
    #
    cpc
    co
    #
    @20
    cle
    wph
    @19
    @22
    cle
    wbr
    #
    @18
    @22
    cN
    cmin
    co
    cle
    wbr
    #
    sylow1lem5.l
    wph
    @18
    cr
    wcel
    cN
    cr
    wcel
    @22
    cr
    wcel
    @23
    @24
    wb
    wph
    @18
    wph
    cP
    @17
    sylow1.p
    wph
    @17
    cn
    wcel
    #
    @16
    c0
    wne
    #
    wph
    cB
    c.sm
    cdm
    #
    wcel
    @26
    wph
    cB
    cS
    @27
    sylow1lem4.b
    wph
    cS
    c.sm
    wer
    #
    @27
    cS
    wceq
    wph
    @8
    @28
    @10
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
    cS
    c.sm
    erdm
    syl
    eleqtrrd
    cB
    c.sm
    ecdmn0
    sylib
    wph
    @16
    cfn
    wcel
    #
    @25
    @26
    wb
    wph
    cS
    cfn
    wcel
    #
    @16
    cS
    wss
    @30
    wph
    cX
    cpw
    #
    cfn
    wcel
    #
    cS
    @32
    wss
    @31
    wph
    cX
    cfn
    wcel
    #
    @33
    sylow1.f
    cX
    pwfi
    sylib
    cS
    vs
    cv
    chash
    cfv
    @3
    wceq
    #
    vs
    @32
    crab
    @32
    sylow1lem.s
    @35
    vs
    @32
    ssrab2
    eqsstri
    @32
    cS
    ssfi
    sylancl
    wph
    cB
    c.sm
    cS
    @29
    ecss
    cS
    @16
    ssfi
    syl2anc
    @16
    hashnncl
    syl
    mpbird
    #
    pccld
    nn0red
    #
    wph
    cN
    sylow1.n
    nn0red
    #
    wph
    @22
    wph
    cP
    @21
    sylow1.p
    wph
    @21
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
    @40
    sylow1.g
    cX
    cG
    sylow1.x
    grpbn0
    syl
    wph
    @34
    @39
    @40
    wb
    sylow1.f
    cX
    hashnncl
    syl
    mpbird
    pccld
    nn0red
    @18
    cN
    @22
    leaddsub
    syl3anc
    mpbird
    wph
    @22
    cP
    @17
    @2
    cmul
    co
    #
    cpc
    co
    #
    @20
    wph
    @21
    @41
    cP
    cpc
    wph
    @8
    @9
    @34
    @21
    @41
    wceq
    @10
    sylow1lem4.b
    sylow1.f
    vx
    vy
    vu
    cB
    c.po
    cG
    cH
    cqg
    co
    #
    vg
    cG
    cH
    c.sm
    cX
    cS
    sylow1.x
    sylow1lem4.h
    @43
    eqid
    sylow1lem3.1
    orbsta2
    syl21anc
    oveq2d
    wph
    cP
    cprime
    wcel
    #
    @17
    cz
    wcel
    @17
    cc0
    wne
    @2
    cz
    wcel
    #
    @2
    cc0
    wne
    @42
    @20
    wceq
    sylow1.p
    wph
    @17
    @36
    nnzd
    wph
    @17
    @36
    nnne0d
    wph
    @2
    wph
    @2
    cn
    wcel
    #
    cH
    c0
    wne
    #
    wph
    cG
    c0g
    cfv
    #
    cH
    wcel
    #
    @47
    wph
    @1
    @49
    @11
    cH
    cG
    @48
    @48
    eqid
    subg0cl
    syl
    cH
    @48
    ne0i
    syl
    wph
    cH
    cfn
    wcel
    #
    @46
    @47
    wb
    wph
    @34
    cH
    cX
    wss
    @50
    sylow1.f
    cH
    vu
    cv
    cB
    c.po
    co
    cB
    wceq
    #
    vu
    cX
    crab
    cX
    sylow1lem4.h
    @51
    vu
    cX
    ssrab2
    eqsstri
    cX
    cH
    ssfi
    sylancl
    #
    cH
    hashnncl
    syl
    mpbird
    #
    nnzd
    #
    wph
    @2
    @53
    nnne0d
    @17
    @2
    cP
    pcmul
    syl122anc
    eqtrd
    breqtrd
    wph
    cN
    @14
    @18
    @38
    wph
    @14
    wph
    cP
    @2
    sylow1.p
    @53
    pccld
    nn0red
    @37
    leadd2d
    mpbird
    wph
    @44
    @45
    cN
    cn0
    wcel
    @15
    @13
    wb
    sylow1.p
    @54
    sylow1.n
    cN
    cP
    @2
    pcdvdsb
    syl3anc
    mpbid
    wph
    @3
    cz
    wcel
    @46
    @13
    @12
    wi
    wph
    @3
    wph
    cP
    cN
    wph
    @44
    cP
    cn
    wcel
    sylow1.p
    cP
    prmnn
    syl
    sylow1.n
    nnexpcld
    #
    nnzd
    @53
    @3
    @2
    dvdsle
    syl2anc
    mpd
    wph
    @2
    @3
    wph
    @2
    wph
    @50
    @2
    cn0
    wcel
    @52
    cH
    hashcl
    syl
    nn0red
    wph
    @3
    @55
    nnred
    letri3d
    mpbir2and
    @7
    @4
    vh
    cH
    @0
    @5
    cH
    wceq
    @6
    @2
    @3
    @5
    cH
    chash
    fveq2
    eqeq1d
    rspcev
    syl2anc
end

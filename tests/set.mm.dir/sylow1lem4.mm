include "chash.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cdom.mm"
include "cv.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wex.mm"
include "cc0.mm"
include "cn.mm"
include "cpw.mm"
include "wceq.mm"
include "wa.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simprd.mm"
include "cprime.mm"
include "prmnn.mm"
include "syl.mm"
include "nnexpcld.mm"
include "eqeltrd.mm"
include "nnne0d.mm"
include "wb.mm"
include "hasheq0.mm"
include "necon3bid.mm"
include "mpbid.mm"
include "n0.mm"
include "adantr.mm"
include "cmpt.mm"
include "crn.mm"
include "simplr.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wfn.mm"
include "fnmpti.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "eqeltrrd.mm"
include "cvv.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "mptexg.mm"
include "rnexg.mm"
include "3syl.mm"
include "weq.mm"
include "simpl.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "rneqd.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "oveq1.mm"
include "simprbi.mm"
include "adantl.mm"
include "eleqtrd.mm"
include "ex.mm"
include "cgrp.mm"
include "simprl.mm"
include "simprr.mm"
include "simpld.mm"
include "elpwid.mm"
include "sselda.mm"
include "grprcan.mm"
include "syl13anc.mm"
include "dom2d.mm"
include "mpd.mm"
include "exlimddv.mm"
include "cfn.mm"
include "wss.mm"
include "ssfi.mm"
include "sylancl.mm"
include "syl2anc.mm"
include "hashdom.mm"
include "mpbird.mm"
include "breqtrd.mm"

theorem sylow1lem4
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
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
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
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint S g
  disjoint S u
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint N g
  disjoint N s
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint X g
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
  disjoint G s
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint P g
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
  disjoint g h
  disjoint h x
  disjoint h y
  disjoint H h
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
  disjoint X h
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
  disjoint G h
  disjoint G k
  disjoint G t
  disjoint G v
  disjoint P a
  disjoint P b
  disjoint P h
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
  assert |- ( ph -> ( # ` H ) <_ ( P ^ N ) )

  proof
    wph
    cH
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cP
    cN
    cexp
    co
    #
    cle
    wph
    @0
    @1
    cle
    wbr
    #
    cH
    cB
    cdom
    wbr
    #
    wph
    va
    cv
    #
    cB
    wcel
    #
    @4
    va
    wph
    cB
    c0
    wne
    #
    @6
    va
    wex
    wph
    @1
    cc0
    wne
    #
    @7
    wph
    @1
    wph
    @1
    @2
    cn
    wph
    cB
    cX
    cpw
    #
    wcel
    #
    @1
    @2
    wceq
    #
    wph
    cB
    cS
    wcel
    #
    @10
    @11
    wa
    sylow1lem4.b
    vs
    cv
    #
    chash
    cfv
    #
    @2
    wceq
    @11
    vs
    cB
    @9
    cS
    @13
    cB
    wceq
    @14
    @1
    @2
    @13
    cB
    chash
    fveq2
    eqeq1d
    sylow1lem.s
    elrab2
    sylib
    #
    simprd
    #
    wph
    cP
    cN
    wph
    cP
    cprime
    wcel
    cP
    cn
    wcel
    sylow1.p
    cP
    prmnn
    syl
    sylow1.n
    nnexpcld
    eqeltrd
    nnne0d
    wph
    @12
    @8
    @7
    wb
    sylow1lem4.b
    @12
    @1
    cc0
    cB
    c0
    cB
    cS
    hasheq0
    necon3bid
    syl
    mpbid
    va
    cB
    n0
    sylib
    wph
    @6
    wa
    #
    @12
    @4
    wph
    @12
    @6
    sylow1lem4.b
    adantr
    @17
    vb
    vc
    cH
    cB
    vb
    cv
    #
    @5
    c.pl
    co
    #
    vc
    cv
    #
    @5
    c.pl
    co
    #
    cS
    @17
    @18
    cH
    wcel
    #
    @19
    cB
    wcel
    @17
    @22
    wa
    #
    @19
    @18
    cB
    c.po
    co
    #
    cB
    @23
    @19
    vz
    cB
    @18
    vz
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    crn
    #
    @24
    @23
    @5
    @27
    cfv
    #
    @19
    @28
    @23
    @6
    @29
    @19
    wceq
    wph
    @6
    @22
    simplr
    #
    vz
    @5
    @26
    @19
    cB
    @27
    @25
    @5
    @18
    c.pl
    oveq2
    @27
    eqid
    #
    @18
    @5
    c.pl
    ovex
    fvmpt
    syl
    @23
    @27
    cB
    wfn
    @6
    @29
    @28
    wcel
    vz
    cB
    @26
    @27
    @18
    @25
    c.pl
    ovex
    @31
    fnmpti
    @30
    cB
    @5
    @27
    fnfvelrn
    sylancr
    eqeltrrd
    @23
    @18
    cX
    wcel
    #
    @12
    @28
    cvv
    wcel
    #
    @24
    @28
    wceq
    @23
    cH
    cX
    @18
    cH
    vu
    cv
    #
    cB
    c.po
    co
    #
    cB
    wceq
    #
    vu
    cX
    crab
    cX
    sylow1lem4.h
    @36
    vu
    cX
    ssrab2
    eqsstri
    #
    @17
    @22
    simpr
    sseldi
    wph
    @12
    @6
    @22
    sylow1lem4.b
    ad2antrr
    #
    @23
    @12
    @27
    cvv
    wcel
    @33
    @38
    vz
    cB
    @26
    cS
    mptexg
    @27
    cvv
    rnexg
    3syl
    vx
    vy
    @18
    cB
    cX
    cS
    vz
    vy
    cv
    #
    vx
    cv
    #
    @25
    c.pl
    co
    #
    cmpt
    #
    crn
    @28
    c.po
    cvv
    vx
    vb
    weq
    #
    @39
    cB
    wceq
    #
    wa
    #
    @42
    @27
    @45
    vz
    @39
    @41
    cB
    @26
    @43
    @44
    simpr
    @45
    @40
    @18
    @25
    c.pl
    @43
    @44
    simpl
    oveq1d
    mpteq12dv
    rneqd
    sylow1lem.m
    ovmpt2ga
    syl3anc
    eleqtrrd
    @22
    @24
    cB
    wceq
    #
    @17
    @22
    @32
    @46
    @36
    @46
    vu
    @18
    cX
    cH
    vu
    vb
    weq
    @35
    @24
    cB
    @34
    @18
    cB
    c.po
    oveq1
    eqeq1d
    sylow1lem4.h
    elrab2
    simprbi
    adantl
    eleqtrd
    ex
    @17
    @22
    @20
    cH
    wcel
    #
    wa
    #
    @19
    @21
    wceq
    vb
    vc
    weq
    wb
    #
    @17
    @48
    wa
    #
    cG
    cgrp
    wcel
    #
    @32
    @20
    cX
    wcel
    @5
    cX
    wcel
    #
    @49
    wph
    @51
    @6
    @48
    sylow1.g
    ad2antrr
    @50
    cH
    cX
    @18
    @37
    @17
    @22
    @47
    simprl
    sseldi
    @50
    cH
    cX
    @20
    @37
    @17
    @22
    @47
    simprr
    sseldi
    @17
    @52
    @48
    wph
    cB
    cX
    @5
    wph
    cB
    cX
    wph
    @10
    @11
    @15
    simpld
    elpwid
    #
    sselda
    adantr
    cX
    c.pl
    cG
    @18
    @20
    @5
    sylow1.x
    sylow1lem.a
    grprcan
    syl13anc
    ex
    dom2d
    mpd
    exlimddv
    wph
    cH
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    @3
    @4
    wb
    wph
    cX
    cfn
    wcel
    #
    cH
    cX
    wss
    @54
    sylow1.f
    @37
    cX
    cH
    ssfi
    sylancl
    wph
    @56
    cB
    cX
    wss
    @55
    sylow1.f
    @53
    cX
    cB
    ssfi
    syl2anc
    cH
    cB
    cfn
    hashdom
    syl2anc
    mpbird
    @16
    breqtrd
end

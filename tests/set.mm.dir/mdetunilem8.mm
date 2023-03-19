include "wf.mm"
include "wa.mm"
include "wf1.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "wi.mm"
include "cur.mm"
include "co.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "wf1o.mm"
include "wcel.mm"
include "simpl.mm"
include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wb.mm"
include "enrefg.mm"
include "syl.mm"
include "f1finf1o.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "crg.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "adantr.mm"
include "mdetunilem7.mm"
include "syl3anc.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp1r.mm"
include "f1f.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "mat1ov.mm"
include "mpt2eq3dva.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "csymg.mm"
include "cbs.mm"
include "cmgp.mm"
include "cmhm.mm"
include "zrhpsgnmhm.mm"
include "mgpbas.mm"
include "mhmf.mm"
include "elsymgbas.mm"
include "mpbird.mm"
include "ringrz.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "ex.mm"
include "wn.mm"
include "wne.mm"
include "wrex.mm"
include "weq.mm"
include "wral.mm"
include "ibar.mm"
include "adantl.mm"
include "dff13.mm"
include "syl6rbbr.mm"
include "notbid.mm"
include "rexnal.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "annim.mm"
include "bitr2i.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "simprrl.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "ifbid.mm"
include "iftrue.mm"
include "eqtr4d.mm"
include "iffalse.mm"
include "eqcomd.mm"
include "pm2.61i.mm"
include "syl6reqr.mm"
include "eqeq1.mm"
include "eqcoms.mm"
include "ifeq1d.mm"
include "ifeq2d.mm"
include "syl5eq.mm"
include "mpt2eq3dv.mm"
include "simpll.mm"
include "simprll.mm"
include "simprlr.mm"
include "simprrr.mm"
include "3jca.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "ad3antrrr.mm"
include "simp1ll.mm"
include "mdetunilem2.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "pm2.61d.mm"

theorem mdetunilem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cE: class E
  let cK: class K
  let cN: class N
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cY: class Y
  let cF: class F
  let cG: class G
  let cH: class H
  assume mdetuni.a: |- A = ( N Mat R )
  assume mdetuni.b: |- B = ( Base ` A )
  assume mdetuni.k: |- K = ( Base ` R )
  assume mdetuni.0g: |- .0. = ( 0g ` R )
  assume mdetuni.1r: |- .1. = ( 1r ` R )
  assume mdetuni.pg: |- .+ = ( +g ` R )
  assume mdetuni.tg: |- .x. = ( .r ` R )
  assume mdetuni.n: |- ( ph -> N e. Fin )
  assume mdetuni.r: |- ( ph -> R e. Ring )
  assume mdetuni.ff: |- ( ph -> D : B --> K )
  assume mdetuni.al: |- ( ph -> A. x e. B A. y e. N A. z e. N ( ( y =/= z /\ A. w e. N ( y x w ) = ( z x w ) ) -> ( D ` x ) = .0. ) )
  assume mdetuni.li: |- ( ph -> A. x e. B A. y e. B A. z e. B A. w e. N ( ( ( x |` ( { w } X. N ) ) = ( ( y |` ( { w } X. N ) ) oF .+ ( z |` ( { w } X. N ) ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( y |` ( ( N \ { w } ) X. N ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( z |` ( ( N \ { w } ) X. N ) ) ) -> ( D ` x ) = ( ( D ` y ) .+ ( D ` z ) ) ) )
  assume mdetuni.sc: |- ( ph -> A. x e. B A. y e. K A. z e. B A. w e. N ( ( ( x |` ( { w } X. N ) ) = ( ( ( { w } X. N ) X. { y } ) oF .x. ( z |` ( { w } X. N ) ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( z |` ( ( N \ { w } ) X. N ) ) ) -> ( D ` x ) = ( y .x. ( D ` z ) ) ) )
  assume mdetunilem8.id: |- ( ph -> ( D ` ( 1r ` A ) ) = .0. )

  disjoint E a
  disjoint E b
  disjoint a b
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint a ph
  disjoint b ph
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint a x
  disjoint b x
  disjoint y z
  disjoint w y
  disjoint a y
  disjoint b y
  disjoint w z
  disjoint a z
  disjoint b z
  disjoint a w
  disjoint b w
  disjoint a b
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B a
  disjoint B b
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K w
  disjoint K a
  disjoint K b
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N w
  disjoint N a
  disjoint N b
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D a
  disjoint D b
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .+ w
  disjoint .0. a
  disjoint .0. b
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint .0. w
  disjoint .1. a
  disjoint .1. b
  disjoint .1. x
  disjoint .1. y
  disjoint .1. z
  disjoint .1. w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint A a
  disjoint A b
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint E w
  disjoint E c
  disjoint E d
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint c w
  disjoint d w
  disjoint e w
  disjoint f w
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint K c
  disjoint K d
  disjoint K e
  disjoint K f
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint N f
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y e
  disjoint Y f
  disjoint .x. e
  disjoint .+ e
  disjoint .0. c
  disjoint .0. d
  disjoint .0. e
  disjoint .1. c
  disjoint .1. d
  disjoint .1. e
  disjoint R e
  disjoint A c
  disjoint A d
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H w
  assert |- ( ( ph /\ E : N --> N ) -> ( D ` ( a e. N , b e. N |-> if ( ( E ` a ) = b , .1. , .0. ) ) ) = .0. )

  proof
    wph
    cN
    cN
    cE
    wf
    #
    wa
    #
    cN
    cN
    cE
    wf1
    #
    va
    vb
    cN
    cN
    va
    cv
    #
    cE
    cfv
    #
    vb
    cv
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    c.0
    wceq
    #
    wph
    @2
    @10
    wi
    @0
    wph
    @2
    @10
    wph
    @2
    wa
    #
    va
    vb
    cN
    cN
    @4
    @5
    cA
    cur
    cfv
    #
    co
    #
    cmpt2
    #
    cD
    cfv
    #
    cE
    cR
    czrh
    cfv
    cN
    cpsgn
    cfv
    ccom
    #
    cfv
    #
    @12
    cD
    cfv
    #
    c.x
    co
    #
    @9
    c.0
    @11
    wph
    cN
    cN
    cE
    wf1o
    #
    @12
    cB
    wcel
    #
    @15
    @19
    wceq
    wph
    @2
    simpl
    wph
    @2
    @20
    wph
    cN
    cN
    cen
    wbr
    #
    cN
    cfn
    wcel
    #
    @2
    @20
    wb
    wph
    @23
    @22
    mdetuni.n
    cN
    cfn
    enrefg
    syl
    mdetuni.n
    cN
    cN
    cE
    f1finf1o
    syl2anc
    biimpa
    #
    wph
    @21
    @2
    wph
    cA
    crg
    wcel
    #
    @21
    wph
    @23
    cR
    crg
    wcel
    #
    @25
    mdetuni.n
    mdetuni.r
    cA
    cR
    cN
    mdetuni.a
    matring
    syl2anc
    cB
    cA
    @12
    mdetuni.b
    @12
    eqid
    #
    ringidcl
    syl
    adantr
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cD
    c.pl
    cR
    c.x
    c.1
    cE
    @12
    cK
    cN
    c.0
    va
    vb
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetuni.0g
    mdetuni.1r
    mdetuni.pg
    mdetuni.tg
    mdetuni.n
    mdetuni.r
    mdetuni.ff
    mdetuni.al
    mdetuni.li
    mdetuni.sc
    mdetunilem7
    syl3anc
    @11
    @14
    @8
    cD
    @11
    va
    vb
    cN
    cN
    @13
    @7
    @11
    @3
    cN
    wcel
    #
    @5
    cN
    wcel
    #
    w3a
    #
    cA
    cR
    @12
    c.1
    @4
    @5
    cN
    c.0
    mdetuni.a
    mdetuni.1r
    mdetuni.0g
    @11
    @28
    @23
    @29
    wph
    @23
    @2
    mdetuni.n
    adantr
    #
    3ad2ant1
    @11
    @28
    @26
    @29
    wph
    @26
    @2
    mdetuni.r
    adantr
    #
    3ad2ant1
    @30
    cN
    cN
    @3
    cE
    @30
    @2
    @0
    wph
    @2
    @28
    @29
    simp1r
    cN
    cN
    cE
    f1f
    syl
    @11
    @28
    @29
    simp2
    ffvelrnd
    @11
    @28
    @29
    simp3
    @27
    mat1ov
    mpt2eq3dva
    fveq2d
    @11
    @19
    @17
    c.0
    c.x
    co
    #
    c.0
    @11
    @18
    c.0
    @17
    c.x
    wph
    @18
    c.0
    wceq
    @2
    mdetunilem8.id
    adantr
    oveq2d
    @11
    @26
    @17
    cK
    wcel
    @33
    c.0
    wceq
    @32
    @11
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    cK
    cE
    @16
    wph
    @35
    cK
    @16
    wf
    #
    @2
    wph
    @16
    @34
    cR
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    @36
    wph
    @26
    @23
    @38
    mdetuni.r
    mdetuni.n
    cN
    cR
    zrhpsgnmhm
    syl2anc
    @35
    cK
    @34
    @37
    @16
    @35
    eqid
    #
    cK
    cR
    @37
    @37
    eqid
    mdetuni.k
    mgpbas
    mhmf
    syl
    adantr
    @11
    cE
    @35
    wcel
    #
    @20
    @24
    @11
    @23
    @40
    @20
    wb
    @31
    cN
    @35
    cE
    @34
    cfn
    @34
    eqid
    @39
    elsymgbas
    syl
    mpbird
    ffvelrnd
    cK
    cR
    c.x
    @17
    c.0
    mdetuni.k
    mdetuni.tg
    mdetuni.0g
    ringrz
    syl2anc
    eqtrd
    3eqtr3d
    ex
    adantr
    @1
    @2
    wn
    #
    vc
    cv
    #
    cE
    cfv
    #
    vd
    cv
    #
    cE
    cfv
    #
    wceq
    #
    @42
    @44
    wne
    #
    wa
    #
    vd
    cN
    wrex
    #
    vc
    cN
    wrex
    #
    @10
    @1
    @41
    @46
    vc
    vd
    weq
    #
    wi
    #
    vd
    cN
    wral
    #
    vc
    cN
    wral
    #
    wn
    #
    @50
    @1
    @2
    @54
    @1
    @54
    @0
    @54
    wa
    #
    @2
    @0
    @54
    @56
    wb
    wph
    @0
    @54
    ibar
    adantl
    vc
    vd
    cN
    cN
    cE
    dff13
    syl6rbbr
    notbid
    @55
    @53
    wn
    #
    vc
    cN
    wrex
    @50
    @53
    vc
    cN
    rexnal
    @57
    @49
    vc
    cN
    @57
    @52
    wn
    #
    vd
    cN
    wrex
    @49
    @52
    vd
    cN
    rexnal
    @58
    @48
    vd
    cN
    @48
    @46
    @51
    wn
    #
    wa
    @58
    @47
    @59
    @46
    @42
    @44
    df-ne
    anbi2i
    @46
    @51
    annim
    bitr2i
    rexbii
    bitr3i
    rexbii
    bitr3i
    syl6bb
    @1
    @48
    @10
    vc
    vd
    cN
    cN
    @1
    @42
    cN
    wcel
    #
    @44
    cN
    wcel
    #
    wa
    #
    @48
    @10
    @1
    @62
    @48
    wa
    #
    wa
    #
    @9
    va
    vb
    cN
    cN
    va
    vc
    weq
    #
    @43
    @5
    wceq
    #
    c.1
    c.0
    cif
    #
    va
    vd
    weq
    #
    @67
    @7
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    c.0
    @64
    @46
    @9
    @72
    wceq
    @1
    @62
    @46
    @47
    simprrl
    @46
    @8
    @71
    cD
    @46
    va
    vb
    cN
    cN
    @7
    @70
    @46
    @7
    @65
    @67
    @68
    @45
    @5
    wceq
    #
    c.1
    c.0
    cif
    #
    @7
    cif
    #
    cif
    #
    @70
    @65
    @7
    @76
    wceq
    @65
    @7
    @67
    @76
    @65
    @6
    @66
    c.1
    c.0
    @65
    @4
    @43
    @5
    @3
    @42
    cE
    fveq2
    eqeq1d
    ifbid
    @65
    @67
    @75
    iftrue
    eqtr4d
    @65
    wn
    @76
    @75
    @7
    @65
    @67
    @75
    iffalse
    @68
    @7
    @75
    wceq
    @68
    @7
    @74
    @75
    @68
    @6
    @73
    c.1
    c.0
    @68
    @4
    @45
    @5
    @3
    @44
    cE
    fveq2
    eqeq1d
    ifbid
    @68
    @74
    @7
    iftrue
    eqtr4d
    @68
    wn
    @75
    @7
    @68
    @74
    @7
    iffalse
    eqcomd
    pm2.61i
    syl6reqr
    pm2.61i
    @46
    @65
    @75
    @69
    @67
    @46
    @68
    @74
    @67
    @7
    @46
    @73
    @66
    c.1
    c.0
    @73
    @66
    wb
    @45
    @43
    @45
    @43
    @5
    eqeq1
    eqcoms
    ifbid
    ifeq1d
    ifeq2d
    syl5eq
    mpt2eq3dv
    fveq2d
    syl
    wph
    @64
    vx
    vy
    vz
    vw
    cA
    cB
    cD
    c.pl
    cR
    c.x
    c.1
    @42
    @67
    @44
    @7
    cK
    cN
    c.0
    va
    vb
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetuni.0g
    mdetuni.1r
    mdetuni.pg
    mdetuni.tg
    mdetuni.n
    mdetuni.r
    mdetuni.ff
    mdetuni.al
    mdetuni.li
    mdetuni.sc
    wph
    @0
    @63
    simpll
    @64
    @60
    @61
    @47
    @1
    @60
    @61
    @48
    simprll
    @1
    @60
    @61
    @48
    simprlr
    @1
    @62
    @46
    @47
    simprrr
    3jca
    wph
    @67
    cK
    wcel
    @0
    @63
    @29
    wph
    @66
    c.1
    c.0
    cK
    wph
    @26
    c.1
    cK
    wcel
    mdetuni.r
    cK
    cR
    c.1
    mdetuni.k
    mdetuni.1r
    ringidcl
    syl
    #
    wph
    @26
    c.0
    cK
    wcel
    mdetuni.r
    cK
    cR
    c.0
    mdetuni.k
    mdetuni.0g
    ring0cl
    syl
    #
    ifcld
    ad3antrrr
    @64
    @28
    @29
    w3a
    wph
    @7
    cK
    wcel
    wph
    @0
    @63
    @28
    @29
    simp1ll
    wph
    @6
    c.1
    c.0
    cK
    @77
    @78
    ifcld
    syl
    mdetunilem2
    eqtrd
    expr
    rexlimdvva
    sylbid
    pm2.61d
end

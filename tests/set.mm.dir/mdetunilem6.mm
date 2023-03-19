include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "cfv.mm"
include "cminusg.mm"
include "co.mm"
include "wcel.mm"
include "wne.mm"
include "simp1d.mm"
include "w3a.mm"
include "wa.mm"
include "simprd.mm"
include "3adant2.mm"
include "simpld.mm"
include "cgrp.mm"
include "crg.mm"
include "ringgrp.mm"
include "3syl.mm"
include "adantr.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "ifcld.mm"
include "3jca.mm"
include "mdetunilem5.mm"
include "mdetunilem2.mm"
include "simp2d.mm"
include "simp3d.mm"
include "necomd.mm"
include "oveq1d.mm"
include "wn.mm"
include "neneqd.mm"
include "eqtr2.mm"
include "nsyl.mm"
include "3ad2ant1.mm"
include "ifcomnan.mm"
include "syl.mm"
include "mpt2eq3dva.mm"
include "fveq2d.mm"
include "wf.mm"
include "cfn.mm"
include "matbas2d.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "grplid.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "grprid.mm"
include "oveq12d.mm"
include "3eqtr3rd.mm"
include "wb.mm"
include "eqid.mm"
include "grpinvid1.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem mdetunilem6
  let wph: wff ph
  let wps: wff ps
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
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
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
  assume mdetunilem6.ph: |- ( ps -> ph )
  assume mdetunilem6.ef: |- ( ps -> ( E e. N /\ F e. N /\ E =/= F ) )
  assume mdetunilem6.gh: |- ( ( ps /\ b e. N ) -> ( G e. K /\ H e. K ) )
  assume mdetunilem6.i: |- ( ( ps /\ a e. N /\ b e. N ) -> I e. K )

  disjoint a ps
  disjoint b ps
  disjoint ps x
  disjoint ps y
  disjoint ps z
  disjoint ps w
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint E a
  disjoint E b
  disjoint F a
  disjoint F b
  disjoint G a
  disjoint H a
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint I w
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
  assert |- ( ps -> ( D ` ( a e. N , b e. N |-> if ( a = E , G , if ( a = F , H , I ) ) ) ) = ( ( invg ` R ) ` ( D ` ( a e. N , b e. N |-> if ( a = E , H , if ( a = F , G , I ) ) ) ) ) )

  proof
    wps
    va
    vb
    cN
    cN
    va
    cv
    #
    cE
    wceq
    #
    cH
    @0
    cF
    wceq
    #
    cG
    cI
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    va
    vb
    cN
    cN
    @1
    cG
    @2
    cH
    cI
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    wps
    @8
    @12
    wceq
    #
    @6
    @12
    c.pl
    co
    #
    c.0
    wceq
    #
    wps
    va
    vb
    cN
    cN
    @1
    cH
    cG
    c.pl
    co
    #
    @2
    @16
    cI
    cif
    #
    cif
    cmpt2
    cD
    cfv
    va
    vb
    cN
    cN
    @1
    cH
    @17
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    va
    vb
    cN
    cN
    @1
    cG
    @17
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    c.pl
    co
    c.0
    @14
    wph
    wps
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
    cH
    cG
    @17
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
    mdetunilem6.ph
    wps
    cE
    cN
    wcel
    #
    cF
    cN
    wcel
    #
    cE
    cF
    wne
    #
    mdetunilem6.ef
    simp1d
    #
    wps
    @0
    cN
    wcel
    #
    vb
    cv
    cN
    wcel
    #
    w3a
    #
    cH
    cK
    wcel
    #
    cG
    cK
    wcel
    #
    @17
    cK
    wcel
    wps
    @29
    @31
    @28
    wps
    @29
    wa
    #
    @32
    @31
    mdetunilem6.gh
    simprd
    #
    3adant2
    #
    wps
    @29
    @32
    @28
    @33
    @32
    @31
    mdetunilem6.gh
    simpld
    #
    3adant2
    #
    @30
    @2
    @16
    cI
    cK
    wps
    @29
    @16
    cK
    wcel
    #
    @28
    @33
    cR
    cgrp
    wcel
    #
    @31
    @32
    @38
    wps
    @39
    @29
    wps
    wph
    cR
    crg
    wcel
    @39
    mdetunilem6.ph
    mdetuni.r
    cR
    ringgrp
    3syl
    #
    adantr
    @34
    @36
    cK
    c.pl
    cR
    cH
    cG
    mdetuni.k
    mdetuni.pg
    grpcl
    syl3anc
    #
    3adant2
    mdetunilem6.i
    ifcld
    3jca
    mdetunilem5
    wph
    wps
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
    @16
    cF
    cI
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
    mdetunilem6.ph
    mdetunilem6.ef
    @41
    mdetunilem6.i
    mdetunilem2
    wps
    @20
    @6
    @23
    @12
    c.pl
    wps
    va
    vb
    cN
    cN
    @2
    @16
    @1
    cH
    cI
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    va
    vb
    cN
    cN
    @2
    cG
    @42
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    @20
    @6
    wps
    @45
    va
    vb
    cN
    cN
    @2
    cH
    @42
    cif
    cmpt2
    cD
    cfv
    #
    @48
    c.pl
    co
    c.0
    @48
    c.pl
    co
    #
    @48
    wph
    wps
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
    cF
    cH
    cG
    @42
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
    mdetunilem6.ph
    wps
    @24
    @25
    @26
    mdetunilem6.ef
    simp2d
    #
    @30
    @31
    @32
    @42
    cK
    wcel
    @35
    @37
    @30
    @1
    cH
    cI
    cK
    @35
    mdetunilem6.i
    ifcld
    3jca
    mdetunilem5
    wps
    @49
    c.0
    @48
    c.pl
    wph
    wps
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
    cF
    cH
    cE
    cI
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
    mdetunilem6.ph
    wps
    @25
    @24
    cF
    cE
    wne
    @51
    @27
    wps
    cE
    cF
    wps
    @24
    @25
    @26
    mdetunilem6.ef
    simp3d
    #
    necomd
    3jca
    #
    @34
    mdetunilem6.i
    mdetunilem2
    oveq1d
    wps
    @39
    @48
    cK
    wcel
    @50
    @48
    wceq
    @40
    wps
    @6
    @48
    cK
    wps
    @5
    @47
    cD
    wps
    va
    vb
    cN
    cN
    @4
    @46
    @30
    @1
    @2
    wa
    #
    wn
    #
    @4
    @46
    wceq
    wps
    @28
    @55
    @29
    wps
    cE
    cF
    wceq
    @54
    wps
    cE
    cF
    @52
    neneqd
    @0
    cE
    cF
    eqtr2
    nsyl
    3ad2ant1
    #
    @1
    @2
    cH
    cG
    cI
    ifcomnan
    syl
    mpt2eq3dva
    fveq2d
    #
    wps
    cB
    cK
    @5
    cD
    wps
    wph
    cB
    cK
    cD
    wf
    mdetunilem6.ph
    mdetuni.ff
    syl
    #
    wps
    va
    vb
    cA
    cB
    @4
    cR
    cK
    cN
    cgrp
    mdetuni.a
    mdetuni.k
    mdetuni.b
    wps
    wph
    cN
    cfn
    wcel
    mdetunilem6.ph
    mdetuni.n
    syl
    #
    @40
    @30
    @1
    cH
    @3
    cK
    @35
    @30
    @2
    cG
    cI
    cK
    @37
    mdetunilem6.i
    ifcld
    ifcld
    matbas2d
    ffvelrnd
    #
    eqeltrrd
    cK
    c.pl
    cR
    @48
    c.0
    mdetuni.k
    mdetuni.pg
    mdetuni.0g
    grplid
    syl2anc
    3eqtrd
    wps
    @19
    @44
    cD
    wps
    va
    vb
    cN
    cN
    @18
    @43
    @30
    @55
    @18
    @43
    wceq
    @56
    @1
    @2
    cH
    @16
    cI
    ifcomnan
    syl
    mpt2eq3dva
    fveq2d
    @57
    3eqtr4d
    wps
    va
    vb
    cN
    cN
    @2
    @16
    @1
    cG
    cI
    cif
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    va
    vb
    cN
    cN
    @2
    cH
    @61
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    @23
    @12
    wps
    @64
    @67
    va
    vb
    cN
    cN
    @2
    cG
    @61
    cif
    cmpt2
    cD
    cfv
    #
    c.pl
    co
    @67
    c.0
    c.pl
    co
    #
    @67
    wph
    wps
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
    cF
    cH
    cG
    @61
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
    mdetunilem6.ph
    @51
    @30
    @31
    @32
    @61
    cK
    wcel
    @35
    @37
    @30
    @1
    cG
    cI
    cK
    @37
    mdetunilem6.i
    ifcld
    3jca
    mdetunilem5
    wps
    @68
    c.0
    @67
    c.pl
    wph
    wps
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
    cF
    cG
    cE
    cI
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
    mdetunilem6.ph
    @53
    @36
    mdetunilem6.i
    mdetunilem2
    oveq2d
    wps
    @39
    @67
    cK
    wcel
    @69
    @67
    wceq
    @40
    wps
    @12
    @67
    cK
    wps
    @11
    @66
    cD
    wps
    va
    vb
    cN
    cN
    @10
    @65
    @30
    @55
    @10
    @65
    wceq
    @56
    @1
    @2
    cG
    cH
    cI
    ifcomnan
    syl
    mpt2eq3dva
    fveq2d
    #
    wps
    cB
    cK
    @11
    cD
    @58
    wps
    va
    vb
    cA
    cB
    @10
    cR
    cK
    cN
    cgrp
    mdetuni.a
    mdetuni.k
    mdetuni.b
    @59
    @40
    @30
    @1
    cG
    @9
    cK
    @37
    @30
    @2
    cH
    cI
    cK
    @35
    mdetunilem6.i
    ifcld
    ifcld
    matbas2d
    ffvelrnd
    #
    eqeltrrd
    cK
    c.pl
    cR
    @67
    c.0
    mdetuni.k
    mdetuni.pg
    mdetuni.0g
    grprid
    syl2anc
    3eqtrd
    wps
    @22
    @63
    cD
    wps
    va
    vb
    cN
    cN
    @21
    @62
    @30
    @55
    @21
    @62
    wceq
    @56
    @1
    @2
    cG
    @16
    cI
    ifcomnan
    syl
    mpt2eq3dva
    fveq2d
    @70
    3eqtr4d
    oveq12d
    3eqtr3rd
    wps
    @39
    @6
    cK
    wcel
    @12
    cK
    wcel
    @13
    @15
    wb
    @40
    @60
    @71
    cK
    c.pl
    cR
    @7
    @6
    @12
    c.0
    mdetuni.k
    mdetuni.pg
    mdetuni.0g
    @7
    eqid
    grpinvid1
    syl3anc
    mpbird
    eqcomd
end

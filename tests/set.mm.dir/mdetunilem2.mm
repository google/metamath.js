include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "wcel.mm"
include "co.mm"
include "wral.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "crg.mm"
include "cfn.mm"
include "syl.mm"
include "3adant2.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "wa.mm"
include "csb.mm"
include "eqidd.mm"
include "weq.mm"
include "iftrue.mm"
include "csbeq1a.mm"
include "sylan9eq.mm"
include "adantl.mm"
include "simp1d.mm"
include "adantr.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nfcv.mm"
include "ovmpt2dxf.mm"
include "wn.mm"
include "simp3d.mm"
include "neeq2.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "necomd.mm"
include "neneqd.mm"
include "adantrr.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "simp2d.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "mdetunilem1.mm"
include "syl31anc.mm"

theorem mdetunilem2
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
  assume mdetunilem2.ph: |- ( ps -> ph )
  assume mdetunilem2.eg: |- ( ps -> ( E e. N /\ G e. N /\ E =/= G ) )
  assume mdetunilem2.f: |- ( ( ps /\ b e. N ) -> F e. K )
  assume mdetunilem2.h: |- ( ( ps /\ a e. N /\ b e. N ) -> H e. K )

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
  disjoint G a
  disjoint G b
  disjoint F a
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
  assert |- ( ps -> ( D ` ( a e. N , b e. N |-> if ( a = E , F , if ( a = G , F , H ) ) ) ) = .0. )

  proof
    wps
    wph
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
    cF
    @0
    cG
    wceq
    #
    cF
    cH
    cif
    #
    cif
    #
    cmpt2
    #
    cB
    wcel
    cE
    vw
    cv
    #
    @5
    co
    #
    cG
    @6
    @5
    co
    #
    wceq
    #
    vw
    cN
    wral
    cE
    cN
    wcel
    #
    cG
    cN
    wcel
    #
    cE
    cG
    wne
    #
    w3a
    @5
    cD
    cfv
    c.0
    wceq
    mdetunilem2.ph
    wps
    va
    vb
    cA
    cB
    @4
    cR
    cK
    cN
    crg
    mdetuni.a
    mdetuni.k
    mdetuni.b
    wps
    wph
    cN
    cfn
    wcel
    mdetunilem2.ph
    mdetuni.n
    syl
    wps
    wph
    cR
    crg
    wcel
    mdetunilem2.ph
    mdetuni.r
    syl
    wps
    @0
    cN
    wcel
    #
    vb
    cv
    #
    cN
    wcel
    #
    w3a
    #
    @1
    cF
    @3
    cK
    wps
    @15
    cF
    cK
    wcel
    #
    @13
    mdetunilem2.f
    3adant2
    #
    @16
    @2
    cF
    cH
    cK
    @18
    mdetunilem2.h
    ifcld
    ifcld
    matbas2d
    wps
    @9
    vw
    cN
    wps
    @6
    cN
    wcel
    #
    wa
    #
    @7
    vb
    @6
    cF
    csb
    #
    @8
    @20
    va
    vb
    cE
    @6
    cN
    cN
    @4
    @21
    @5
    cN
    cK
    @20
    @5
    eqidd
    #
    @1
    vb
    vw
    weq
    #
    wa
    @4
    @21
    wceq
    @20
    @1
    @23
    @4
    cF
    @21
    @1
    cF
    @3
    iftrue
    vb
    @6
    cF
    csbeq1a
    #
    sylan9eq
    adantl
    @20
    @1
    wa
    cN
    eqidd
    wps
    @10
    @19
    wps
    @10
    @11
    @12
    mdetunilem2.eg
    simp1d
    adantr
    wps
    @19
    simpr
    #
    wps
    @15
    wa
    #
    @17
    wi
    @20
    @21
    cK
    wcel
    #
    wi
    vb
    vw
    @20
    @27
    vb
    @20
    vb
    nfv
    #
    vb
    @21
    cK
    vb
    @6
    cF
    nfcsb1v
    #
    nfel1
    nfim
    @23
    @26
    @20
    @17
    @27
    @23
    @15
    @19
    wps
    @14
    @6
    cN
    eleq1
    anbi2d
    @23
    cF
    @21
    cK
    @24
    eleq1d
    imbi12d
    mdetunilem2.f
    chvar
    #
    @20
    va
    nfv
    #
    @28
    vb
    cE
    nfcv
    va
    @6
    nfcv
    #
    va
    @21
    nfcv
    #
    @29
    ovmpt2dxf
    @20
    va
    vb
    cG
    @6
    cN
    cN
    @4
    @21
    @5
    cN
    cK
    @22
    @20
    @2
    @23
    wa
    #
    wa
    #
    @4
    @3
    @21
    @35
    @1
    cF
    @3
    @20
    @2
    @1
    wn
    @23
    @20
    @2
    wa
    #
    @0
    cE
    @36
    cE
    @0
    @20
    @2
    cE
    @0
    wne
    #
    @20
    @37
    @2
    @12
    wps
    @12
    @19
    wps
    @10
    @11
    @12
    mdetunilem2.eg
    simp3d
    adantr
    @0
    cG
    cE
    neeq2
    syl5ibrcom
    imp
    necomd
    neneqd
    adantrr
    iffalsed
    @34
    @3
    @21
    wceq
    @20
    @2
    @23
    @3
    cF
    @21
    @2
    cF
    cH
    iftrue
    @24
    sylan9eq
    adantl
    eqtrd
    @36
    cN
    eqidd
    wps
    @11
    @19
    wps
    @10
    @11
    @12
    mdetunilem2.eg
    simp2d
    adantr
    @25
    @30
    @31
    @28
    vb
    cG
    nfcv
    @32
    @33
    @29
    ovmpt2dxf
    eqtr4d
    ralrimiva
    mdetunilem2.eg
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
    @5
    cE
    cG
    cK
    cN
    c.0
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
    mdetunilem1
    syl31anc
end

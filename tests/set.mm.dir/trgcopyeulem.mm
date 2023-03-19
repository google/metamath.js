include "co.mm"
include "clmi.mm"
include "cfv.mm"
include "ncoltgdim2.mm"
include "eqid.mm"
include "ncolne1.mm"
include "tgelrnln.mm"
include "wceq.mm"
include "cmid.mm"
include "wcel.mm"
include "cperpg.mm"
include "wbr.mm"
include "wo.mm"
include "wa.mm"
include "cv.mm"
include "cmir.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "crn.mm"
include "simplr.mm"
include "tglnpt.mm"
include "lmicl.mm"
include "ccgrg.mm"
include "wne.mm"
include "necomd.mm"
include "lncom.mm"
include "orcd.mm"
include "colrot1.mm"
include "cgr3simp3.mm"
include "tgcgrcomlr.mm"
include "eqtr3d.mm"
include "lmiiso.mm"
include "tglinerflx1.mm"
include "lmicinv.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "cgr3simp2.mm"
include "tglinerflx2.mm"
include "lncgr.mm"
include "simpr.mm"
include "ismir.mm"
include "eqcomd.mm"
include "mircom.mm"
include "c2.mm"
include "cstrkgld.mm"
include "ismidb.mm"
include "mpbid.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wrex.mm"
include "chpg.mm"
include "hpgcom.mm"
include "hpgtr.mm"
include "hpgne1.mm"
include "lmiopp.mm"
include "lnopp2hpgb.mm"
include "mpbird.mm"
include "islnopp.mm"
include "simprd.mm"
include "r19.29a.mm"
include "adantr.mm"
include "oppne3.mm"
include "cin.mm"
include "btwnlng1.mm"
include "elind.mm"
include "ad3antrrr.mm"
include "simplld.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "cs3.mm"
include "crag.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "israg.mm"
include "ragperp.mm"
include "neneor.mm"
include "syl.mm"
include "mpjaodan.mm"
include "jca.mm"
include "islmib.mm"
include "lmieq.mm"

theorem trgcopyeulem
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cO: class O
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vq: setvar q
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume trgcopy.p: |- P = ( Base ` G )
  assume trgcopy.m: |- .- = ( dist ` G )
  assume trgcopy.i: |- I = ( Itv ` G )
  assume trgcopy.l: |- L = ( LineG ` G )
  assume trgcopy.k: |- K = ( hlG ` G )
  assume trgcopy.g: |- ( ph -> G e. TarskiG )
  assume trgcopy.a: |- ( ph -> A e. P )
  assume trgcopy.b: |- ( ph -> B e. P )
  assume trgcopy.c: |- ( ph -> C e. P )
  assume trgcopy.d: |- ( ph -> D e. P )
  assume trgcopy.e: |- ( ph -> E e. P )
  assume trgcopy.f: |- ( ph -> F e. P )
  assume trgcopy.1: |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) )
  assume trgcopy.2: |- ( ph -> -. ( D e. ( E L F ) \/ E = F ) )
  assume trgcopy.3: |- ( ph -> ( A .- B ) = ( D .- E ) )
  assume trgcopyeulem.o: |- O = { <. a , b >. | ( ( a e. ( P \ ( D L E ) ) /\ b e. ( P \ ( D L E ) ) ) /\ E. t e. ( D L E ) t e. ( a I b ) ) }
  assume trgcopyeulem.x: |- ( ph -> X e. P )
  assume trgcopyeulem.y: |- ( ph -> Y e. P )
  assume trgcopyeulem.1: |- ( ph -> <" A B C "> ( cgrG ` G ) <" D E X "> )
  assume trgcopyeulem.2: |- ( ph -> <" A B C "> ( cgrG ` G ) <" D E Y "> )
  assume trgcopyeulem.3: |- ( ph -> X ( ( hpG ` G ) ` ( D L E ) ) F )
  assume trgcopyeulem.4: |- ( ph -> Y ( ( hpG ` G ) ` ( D L E ) ) F )

  disjoint O a
  disjoint O b
  disjoint O t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint X a
  disjoint X b
  disjoint X t
  disjoint Y a
  disjoint Y b
  disjoint Y t
  disjoint .- a
  disjoint .- b
  disjoint .- t
  disjoint a b
  disjoint a t
  disjoint b t
  disjoint A a
  disjoint A b
  disjoint A t
  disjoint B a
  disjoint B b
  disjoint B t
  disjoint C a
  disjoint C b
  disjoint C t
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint E a
  disjoint E b
  disjoint E t
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint L a
  disjoint L b
  disjoint L t
  disjoint P a
  disjoint P b
  disjoint P t
  disjoint a ph
  disjoint b ph
  disjoint ph t
  disjoint K a
  disjoint .- f
  disjoint .- j
  disjoint .- k
  disjoint .- l
  disjoint .- q
  disjoint .- v
  disjoint .- w
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint a f
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a q
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b f
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b q
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f j
  disjoint f k
  disjoint f l
  disjoint f q
  disjoint f t
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint j k
  disjoint j l
  disjoint j q
  disjoint j t
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k l
  disjoint k q
  disjoint k t
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint l q
  disjoint l t
  disjoint l v
  disjoint l w
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint q t
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A l
  disjoint A q
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B q
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C j
  disjoint C k
  disjoint C l
  disjoint C q
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D l
  disjoint D q
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E f
  disjoint E j
  disjoint E k
  disjoint E l
  disjoint E q
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F f
  disjoint F j
  disjoint F k
  disjoint F l
  disjoint F q
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G j
  disjoint G k
  disjoint G l
  disjoint G q
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I f
  disjoint I j
  disjoint I k
  disjoint I l
  disjoint I q
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint L f
  disjoint L j
  disjoint L k
  disjoint L l
  disjoint L q
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint P f
  disjoint P j
  disjoint P k
  disjoint P l
  disjoint P q
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint f ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph q
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint K f
  disjoint K j
  disjoint K k
  disjoint K l
  assert |- ( ph -> X = Y )

  proof
    wph
    cX
    cY
    cD
    cE
    cL
    co
    #
    cP
    cG
    cI
    cL
    @0
    cG
    clmi
    cfv
    cfv
    #
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    trgcopy.p
    trgcopy.l
    trgcopy.i
    trgcopy.g
    trgcopy.b
    trgcopy.c
    trgcopy.a
    trgcopy.1
    ncoltgdim2
    #
    @1
    eqid
    #
    trgcopy.l
    wph
    cP
    cG
    cI
    cL
    cD
    cE
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopy.d
    trgcopy.e
    wph
    cP
    cG
    cI
    cL
    cD
    cE
    cF
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopy.d
    trgcopy.e
    trgcopy.f
    trgcopy.2
    ncolne1
    #
    tgelrnln
    #
    trgcopyeulem.x
    trgcopyeulem.y
    wph
    cY
    @1
    cfv
    #
    cX
    @1
    cfv
    #
    wph
    @6
    @7
    wceq
    cX
    @6
    cG
    cmid
    cfv
    co
    #
    @0
    wcel
    #
    @0
    cX
    @6
    cL
    co
    #
    cG
    cperpg
    cfv
    wbr
    #
    cX
    @6
    wceq
    #
    wo
    #
    wa
    wph
    @9
    @13
    wph
    vt
    cv
    #
    cX
    @6
    cI
    co
    wcel
    #
    @9
    vt
    @0
    wph
    @14
    @0
    wcel
    #
    wa
    #
    @15
    wa
    #
    @8
    @14
    @0
    @18
    @6
    cX
    @14
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    wceq
    @8
    @14
    wceq
    @18
    @21
    @6
    @18
    @14
    @6
    cX
    cP
    @19
    cG
    cI
    cL
    @20
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @19
    eqid
    #
    wph
    cG
    cstrkg
    wcel
    #
    @16
    @15
    trgcopy.g
    ad2antrr
    #
    @18
    @0
    cP
    cG
    cI
    cL
    @14
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @24
    wph
    @0
    cL
    crn
    #
    wcel
    #
    @16
    @15
    @5
    ad2antrr
    #
    wph
    @16
    @15
    simplr
    #
    tglnpt
    #
    @20
    eqid
    #
    wph
    @6
    cP
    wcel
    @16
    @15
    wph
    cY
    @0
    cP
    cG
    cI
    cL
    @1
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    @2
    @3
    trgcopy.l
    @5
    trgcopyeulem.y
    lmicl
    #
    ad2antrr
    #
    @18
    cX
    @6
    @20
    cfv
    @18
    @14
    @6
    cX
    cP
    @19
    cG
    cI
    cL
    @20
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @22
    @24
    @29
    @30
    @32
    wph
    cX
    cP
    wcel
    #
    @16
    @15
    trgcopyeulem.x
    ad2antrr
    #
    @18
    cX
    @6
    cP
    cG
    ccgrg
    cfv
    #
    cG
    cI
    cL
    c.mi
    cD
    cE
    @14
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @24
    wph
    cD
    cP
    wcel
    #
    @16
    @15
    trgcopy.d
    ad2antrr
    #
    wph
    cE
    cP
    wcel
    #
    @16
    @15
    trgcopy.e
    ad2antrr
    #
    @29
    @35
    eqid
    #
    @34
    @32
    trgcopy.m
    wph
    cD
    cE
    wne
    @16
    @15
    @4
    ad2antrr
    #
    @18
    cP
    cG
    cI
    cL
    cE
    cD
    @14
    trgcopy.p
    trgcopy.l
    trgcopy.i
    @24
    @39
    @37
    @29
    @18
    @14
    cE
    cD
    cL
    co
    wcel
    cE
    cD
    wceq
    @18
    cP
    cG
    cI
    cL
    cE
    cD
    @14
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @24
    @39
    @37
    @29
    @18
    cD
    cE
    @41
    necomd
    #
    @28
    lncom
    orcd
    colrot1
    wph
    cD
    cX
    c.mi
    co
    #
    cD
    @6
    c.mi
    co
    #
    wceq
    @16
    @15
    wph
    @43
    cD
    cY
    c.mi
    co
    #
    cD
    @1
    cfv
    #
    @6
    c.mi
    co
    @44
    wph
    cA
    cC
    c.mi
    co
    @43
    @45
    wph
    cC
    cA
    cX
    cD
    cP
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    trgcopy.c
    trgcopy.a
    trgcopyeulem.x
    trgcopy.d
    wph
    cA
    cB
    cC
    cD
    cP
    @35
    cE
    cX
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @40
    trgcopy.g
    trgcopy.a
    trgcopy.b
    trgcopy.c
    trgcopy.d
    trgcopy.e
    trgcopyeulem.x
    trgcopyeulem.1
    cgr3simp3
    tgcgrcomlr
    wph
    cC
    cA
    cY
    cD
    cP
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    trgcopy.c
    trgcopy.a
    trgcopyeulem.y
    trgcopy.d
    wph
    cA
    cB
    cC
    cD
    cP
    @35
    cE
    cY
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @40
    trgcopy.g
    trgcopy.a
    trgcopy.b
    trgcopy.c
    trgcopy.d
    trgcopy.e
    trgcopyeulem.y
    trgcopyeulem.2
    cgr3simp3
    tgcgrcomlr
    eqtr3d
    wph
    cD
    cY
    @0
    cP
    cG
    cI
    cL
    @1
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    @2
    @3
    trgcopy.l
    @5
    trgcopy.d
    trgcopyeulem.y
    lmiiso
    wph
    @46
    cD
    @6
    c.mi
    wph
    cD
    @0
    cP
    cG
    cI
    cL
    @1
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    @2
    @3
    trgcopy.l
    @5
    trgcopy.d
    wph
    cP
    cD
    cE
    cG
    cI
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopy.d
    trgcopy.e
    @4
    tglinerflx1
    #
    lmicinv
    oveq1d
    3eqtr2d
    ad2antrr
    #
    wph
    cE
    cX
    c.mi
    co
    #
    cE
    @6
    c.mi
    co
    #
    wceq
    @16
    @15
    wph
    @49
    cE
    cY
    c.mi
    co
    #
    cE
    @1
    cfv
    #
    @6
    c.mi
    co
    @50
    wph
    cB
    cC
    c.mi
    co
    @49
    @51
    wph
    cA
    cB
    cC
    cD
    cP
    @35
    cE
    cX
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @40
    trgcopy.g
    trgcopy.a
    trgcopy.b
    trgcopy.c
    trgcopy.d
    trgcopy.e
    trgcopyeulem.x
    trgcopyeulem.1
    cgr3simp2
    wph
    cA
    cB
    cC
    cD
    cP
    @35
    cE
    cY
    cG
    cI
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @40
    trgcopy.g
    trgcopy.a
    trgcopy.b
    trgcopy.c
    trgcopy.d
    trgcopy.e
    trgcopyeulem.y
    trgcopyeulem.2
    cgr3simp2
    eqtr3d
    wph
    cE
    cY
    @0
    cP
    cG
    cI
    cL
    @1
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    @2
    @3
    trgcopy.l
    @5
    trgcopy.e
    trgcopyeulem.y
    lmiiso
    wph
    @52
    cE
    @6
    c.mi
    wph
    cE
    @0
    cP
    cG
    cI
    cL
    @1
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    @2
    @3
    trgcopy.l
    @5
    trgcopy.e
    wph
    cP
    cD
    cE
    cG
    cI
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopy.d
    trgcopy.e
    @4
    tglinerflx2
    #
    lmicinv
    oveq1d
    3eqtr2d
    ad2antrr
    #
    lncgr
    @17
    @15
    simpr
    #
    ismir
    eqcomd
    mircom
    eqcomd
    #
    @18
    cX
    @6
    cP
    @19
    cG
    cI
    @14
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    @24
    wph
    cG
    c2
    cstrkgld
    wbr
    @16
    @15
    @2
    ad2antrr
    @34
    @32
    @22
    @29
    ismidb
    mpbid
    @28
    eqeltrd
    wph
    cX
    @0
    wcel
    wn
    #
    @6
    @0
    wcel
    wn
    #
    wa
    #
    @15
    vt
    @0
    wrex
    #
    wph
    cX
    @6
    cO
    wbr
    #
    @59
    @60
    wa
    wph
    @61
    cY
    cX
    @0
    cG
    chpg
    cfv
    cfv
    wbr
    wph
    vt
    cY
    cF
    cX
    @0
    cP
    cG
    cI
    cL
    cO
    va
    vb
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    @5
    trgcopyeulem.y
    trgcopyeulem.o
    trgcopy.f
    trgcopyeulem.4
    trgcopyeulem.x
    wph
    vt
    cX
    cF
    @0
    cP
    cG
    cI
    cL
    cO
    va
    vb
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    @5
    trgcopyeulem.x
    trgcopyeulem.o
    trgcopy.f
    trgcopyeulem.3
    hpgcom
    hpgtr
    wph
    vt
    cY
    cX
    @6
    @0
    cP
    cG
    cI
    cL
    cO
    va
    vb
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopyeulem.o
    trgcopy.g
    @5
    trgcopyeulem.y
    trgcopyeulem.x
    @31
    wph
    vt
    cY
    @0
    cP
    cG
    cI
    cL
    @1
    c.mi
    cO
    va
    vb
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    trgcopy.g
    @2
    @5
    trgcopyeulem.o
    @3
    trgcopyeulem.y
    wph
    vt
    cY
    cF
    @0
    cP
    cG
    cI
    cL
    cO
    va
    vb
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopyeulem.o
    trgcopy.g
    @5
    trgcopyeulem.y
    trgcopy.f
    trgcopyeulem.4
    hpgne1
    lmiopp
    lnopp2hpgb
    mpbird
    #
    wph
    vt
    cX
    @6
    @0
    cP
    cG
    cI
    c.mi
    cO
    va
    vb
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopyeulem.o
    trgcopyeulem.x
    @31
    islnopp
    mpbid
    #
    simprd
    #
    r19.29a
    wph
    @15
    @13
    vt
    @0
    @18
    @11
    @12
    @18
    cE
    @14
    wne
    #
    @11
    cD
    @14
    wne
    #
    @18
    @65
    wa
    #
    @0
    @10
    cP
    cE
    cG
    cI
    cL
    c.mi
    cX
    @14
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @18
    @23
    @65
    @24
    adantr
    #
    @18
    @26
    @65
    @27
    adantr
    @18
    @10
    @25
    wcel
    #
    @65
    wph
    @69
    @16
    @15
    wph
    cP
    cG
    cI
    cL
    cX
    @6
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopyeulem.x
    @31
    wph
    vt
    cX
    @6
    @0
    cP
    cG
    cI
    cL
    c.mi
    cO
    va
    vb
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopyeulem.o
    trgcopy.l
    @5
    trgcopy.g
    trgcopyeulem.x
    @31
    @62
    oppne3
    #
    tgelrnln
    ad2antrr
    #
    adantr
    @18
    @14
    @0
    @10
    cin
    wcel
    #
    @65
    @18
    @0
    @10
    @14
    @28
    @18
    cP
    cG
    cI
    cL
    cX
    @6
    @14
    trgcopy.p
    trgcopy.i
    trgcopy.l
    @24
    @34
    @32
    @29
    wph
    cX
    @6
    wne
    @16
    @15
    @70
    ad2antrr
    @55
    btwnlng1
    elind
    #
    adantr
    wph
    cE
    @0
    wcel
    @16
    @15
    @65
    @53
    ad3antrrr
    wph
    cX
    @10
    wcel
    #
    @16
    @15
    @65
    wph
    cP
    cX
    @6
    cG
    cI
    cL
    trgcopy.p
    trgcopy.i
    trgcopy.l
    trgcopy.g
    trgcopyeulem.x
    @31
    @70
    tglinerflx1
    #
    ad3antrrr
    @18
    @65
    simpr
    @18
    cX
    @14
    wne
    #
    @65
    @18
    @14
    cX
    @18
    @16
    @57
    @14
    cX
    wne
    @28
    wph
    @57
    @16
    @15
    wph
    @57
    @58
    @60
    @63
    simplld
    ad2antrr
    @14
    cX
    @0
    nelne2
    syl2anc
    necomd
    #
    adantr
    @67
    cE
    @14
    cX
    cs3
    cG
    crag
    cfv
    #
    wcel
    @49
    cE
    @21
    c.mi
    co
    #
    wceq
    #
    @18
    @80
    @65
    @18
    @49
    @50
    @79
    @54
    @18
    @6
    @21
    cE
    c.mi
    @56
    oveq2d
    eqtrd
    adantr
    @67
    cE
    @14
    cX
    cP
    @19
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @22
    @68
    @18
    @38
    @65
    @39
    adantr
    @18
    @14
    cP
    wcel
    #
    @65
    @29
    adantr
    @18
    @33
    @65
    @34
    adantr
    israg
    mpbird
    ragperp
    @18
    @66
    wa
    #
    @0
    @10
    cP
    cD
    cG
    cI
    cL
    c.mi
    cX
    @14
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @18
    @23
    @66
    @24
    adantr
    #
    @18
    @26
    @66
    @27
    adantr
    @18
    @69
    @66
    @71
    adantr
    @18
    @72
    @66
    @73
    adantr
    wph
    cD
    @0
    wcel
    @16
    @15
    @66
    @47
    ad3antrrr
    wph
    @74
    @16
    @15
    @66
    @75
    ad3antrrr
    @18
    @66
    simpr
    @18
    @76
    @66
    @77
    adantr
    @82
    cD
    @14
    cX
    cs3
    @78
    wcel
    @43
    cD
    @21
    c.mi
    co
    #
    wceq
    #
    @18
    @85
    @66
    @18
    @43
    @44
    @84
    @48
    @18
    @6
    @21
    cD
    c.mi
    @56
    oveq2d
    eqtrd
    adantr
    @82
    cD
    @14
    cX
    cP
    @19
    cG
    cI
    cL
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.l
    @22
    @83
    @18
    @36
    @66
    @37
    adantr
    @18
    @81
    @66
    @29
    adantr
    @18
    @33
    @66
    @34
    adantr
    israg
    mpbird
    ragperp
    @18
    cE
    cD
    wne
    @65
    @66
    wo
    @42
    cE
    cD
    @14
    neneor
    syl
    mpjaodan
    orcd
    @64
    r19.29a
    jca
    wph
    cX
    @6
    @0
    cP
    cG
    cI
    cL
    @1
    c.mi
    trgcopy.p
    trgcopy.m
    trgcopy.i
    trgcopy.g
    @2
    @3
    trgcopy.l
    @5
    trgcopyeulem.x
    @31
    islmib
    mpbird
    eqcomd
    lmieq
end

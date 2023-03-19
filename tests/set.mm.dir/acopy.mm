include "cv.mm"
include "chlg.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cs3.mm"
include "ccgra.mm"
include "chpg.mm"
include "wrex.mm"
include "wcel.mm"
include "ccgrg.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wo.mm"
include "wn.mm"
include "simprl.mm"
include "hlln.mm"
include "hlne1.mm"
include "ncolncol.mm"
include "simprr.mm"
include "eqcomd.mm"
include "tgcgrcomlr.mm"
include "trgcopy.mm"
include "wne.mm"
include "ncolne1.mm"
include "ad4antr.mm"
include "ncolrot1.mm"
include "simpr.mm"
include "cgrcgra.mm"
include "hlcomd.mm"
include "cgrahl1.mm"
include "ex.mm"
include "crn.mm"
include "tgelrnln.mm"
include "tglinerflx2.mm"
include "tglinethru.mm"
include "fveq2d.mm"
include "breqd.mm"
include "mpbird.mm"
include "anim12d.mm"
include "reximdva.mm"
include "mpd.mm"
include "necomd.mm"
include "hlcgrex.mm"
include "r19.29a.mm"

theorem acopy
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dfcgra2.p: |- P = ( Base ` G )
  assume dfcgra2.i: |- I = ( Itv ` G )
  assume dfcgra2.m: |- .- = ( dist ` G )
  assume dfcgra2.g: |- ( ph -> G e. TarskiG )
  assume dfcgra2.a: |- ( ph -> A e. P )
  assume dfcgra2.b: |- ( ph -> B e. P )
  assume dfcgra2.c: |- ( ph -> C e. P )
  assume dfcgra2.d: |- ( ph -> D e. P )
  assume dfcgra2.e: |- ( ph -> E e. P )
  assume dfcgra2.f: |- ( ph -> F e. P )
  assume acopy.l: |- L = ( LineG ` G )
  assume acopy.1: |- ( ph -> -. ( A e. ( B L C ) \/ B = C ) )
  assume acopy.2: |- ( ph -> -. ( D e. ( E L F ) \/ E = F ) )

  disjoint .- f
  disjoint A f
  disjoint B f
  disjoint C f
  disjoint D f
  disjoint E f
  disjoint F f
  disjoint G f
  disjoint I f
  disjoint P f
  disjoint L f
  disjoint f ph
  disjoint .- a
  disjoint .- c
  disjoint .- d
  disjoint .- t
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint c d
  disjoint c f
  disjoint c t
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d f
  disjoint d t
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A c
  disjoint A d
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B c
  disjoint B d
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C a
  disjoint C c
  disjoint C d
  disjoint C t
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D a
  disjoint D c
  disjoint D d
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E a
  disjoint E c
  disjoint E d
  disjoint E t
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F a
  disjoint F c
  disjoint F d
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G a
  disjoint G c
  disjoint G d
  disjoint G t
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint I a
  disjoint I c
  disjoint I d
  disjoint I t
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P a
  disjoint P c
  disjoint P d
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint L d
  disjoint a ph
  disjoint c ph
  disjoint d ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> E. f e. P ( <" A B C "> ( cgrA ` G ) <" D E f "> /\ f ( ( hpG ` G ) ` ( D L E ) ) F ) )

  proof
    wph
    vd
    cv
    #
    cD
    cE
    cG
    chlg
    cfv
    #
    cfv
    wbr
    #
    cE
    @0
    c.mi
    co
    #
    cB
    cA
    c.mi
    co
    #
    wceq
    #
    wa
    #
    cA
    cB
    cC
    cs3
    #
    cD
    cE
    vf
    cv
    #
    cs3
    cG
    ccgra
    cfv
    wbr
    #
    @8
    cF
    cD
    cE
    cL
    co
    #
    cG
    chpg
    cfv
    #
    cfv
    #
    wbr
    #
    wa
    #
    vf
    cP
    wrex
    #
    vd
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @6
    wa
    #
    @7
    @0
    cE
    @8
    cs3
    cG
    ccgrg
    cfv
    wbr
    #
    @8
    cF
    @0
    cE
    cL
    co
    #
    @11
    cfv
    #
    wbr
    #
    wa
    #
    vf
    cP
    wrex
    @15
    @18
    cA
    cB
    cC
    @0
    cP
    vf
    cE
    cF
    cG
    cI
    @1
    cL
    c.mi
    dfcgra2.p
    dfcgra2.m
    dfcgra2.i
    acopy.l
    @1
    eqid
    #
    wph
    cG
    cstrkg
    wcel
    #
    @16
    @6
    dfcgra2.g
    ad2antrr
    #
    wph
    cA
    cP
    wcel
    #
    @16
    @6
    dfcgra2.a
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    #
    @16
    @6
    dfcgra2.b
    ad2antrr
    #
    wph
    cC
    cP
    wcel
    #
    @16
    @6
    dfcgra2.c
    ad2antrr
    #
    wph
    @16
    @6
    simplr
    #
    wph
    cE
    cP
    wcel
    #
    @16
    @6
    dfcgra2.e
    ad2antrr
    #
    wph
    cF
    cP
    wcel
    @16
    @6
    dfcgra2.f
    ad2antrr
    #
    wph
    cA
    cB
    cC
    cL
    co
    wcel
    cB
    cC
    wceq
    wo
    wn
    @16
    @6
    acopy.1
    ad2antrr
    @18
    cD
    cE
    cF
    @0
    cP
    cG
    cI
    cL
    dfcgra2.p
    dfcgra2.i
    acopy.l
    @26
    wph
    cD
    cP
    wcel
    #
    @16
    @6
    dfcgra2.d
    ad2antrr
    #
    @35
    @36
    @33
    wph
    cD
    cE
    cF
    cL
    co
    wcel
    cE
    cF
    wceq
    wo
    wn
    @16
    @6
    acopy.2
    ad2antrr
    @18
    @0
    cD
    cE
    cP
    cG
    cI
    @1
    cL
    dfcgra2.p
    dfcgra2.i
    @24
    @33
    @38
    @35
    @26
    acopy.l
    @17
    @2
    @5
    simprl
    #
    hlln
    #
    @18
    @0
    cD
    cE
    cP
    cG
    cI
    @1
    cstrkg
    dfcgra2.p
    dfcgra2.i
    @24
    @33
    @38
    @35
    @26
    @39
    hlne1
    #
    ncolncol
    @18
    cB
    cA
    cE
    @0
    cP
    cG
    cI
    c.mi
    dfcgra2.p
    dfcgra2.m
    dfcgra2.i
    @26
    @30
    @28
    @35
    @33
    @18
    @3
    @4
    @17
    @2
    @5
    simprr
    eqcomd
    tgcgrcomlr
    trgcopy
    @18
    @23
    @14
    vf
    cP
    @18
    @8
    cP
    wcel
    #
    wa
    #
    @19
    @9
    @22
    @13
    @43
    @19
    @9
    @43
    @19
    wa
    #
    cA
    cB
    cC
    @0
    cP
    cE
    @8
    cG
    cI
    @1
    cD
    dfcgra2.p
    dfcgra2.i
    @24
    @18
    @25
    @42
    @19
    @26
    ad2antrr
    #
    @18
    @27
    @42
    @19
    @28
    ad2antrr
    #
    @18
    @29
    @42
    @19
    @30
    ad2antrr
    #
    @18
    @31
    @42
    @19
    @32
    ad2antrr
    #
    @18
    @16
    @42
    @19
    @33
    ad2antrr
    #
    @18
    @34
    @42
    @19
    @35
    ad2antrr
    #
    @18
    @42
    @19
    simplr
    #
    @44
    cA
    cB
    cC
    @0
    cP
    cE
    @8
    cG
    cI
    @1
    dfcgra2.p
    dfcgra2.i
    @45
    @24
    @46
    @47
    @48
    @49
    @50
    @51
    wph
    cA
    cB
    wne
    @16
    @6
    @42
    @19
    wph
    cP
    cG
    cI
    cL
    cA
    cB
    cC
    dfcgra2.p
    dfcgra2.i
    acopy.l
    dfcgra2.g
    dfcgra2.a
    dfcgra2.b
    dfcgra2.c
    acopy.1
    ncolne1
    #
    ad4antr
    wph
    cB
    cC
    wne
    @16
    @6
    @42
    @19
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    dfcgra2.p
    dfcgra2.i
    acopy.l
    dfcgra2.g
    dfcgra2.b
    dfcgra2.c
    dfcgra2.a
    wph
    cP
    cG
    cI
    cL
    cB
    cC
    cA
    dfcgra2.p
    acopy.l
    dfcgra2.i
    dfcgra2.g
    dfcgra2.b
    dfcgra2.c
    dfcgra2.a
    acopy.1
    ncolrot1
    ncolne1
    ad4antr
    @43
    @19
    simpr
    cgrcgra
    @18
    @37
    @42
    @19
    @38
    ad2antrr
    #
    @44
    @0
    cD
    cE
    cP
    cG
    cI
    @1
    cstrkg
    dfcgra2.p
    dfcgra2.i
    @24
    @49
    @53
    @50
    @45
    @18
    @2
    @42
    @19
    @39
    ad2antrr
    hlcomd
    cgrahl1
    ex
    @43
    @22
    @13
    @43
    @22
    wa
    #
    @13
    @22
    @43
    @22
    simpr
    @54
    @12
    @21
    @8
    cF
    @54
    @10
    @20
    @11
    @54
    @10
    cP
    @0
    cE
    cG
    cI
    cL
    dfcgra2.p
    dfcgra2.i
    acopy.l
    @18
    @25
    @42
    @22
    @26
    ad2antrr
    @18
    @16
    @42
    @22
    @33
    ad2antrr
    @18
    @34
    @42
    @22
    @35
    ad2antrr
    @18
    @0
    cE
    wne
    @42
    @22
    @41
    ad2antrr
    #
    @55
    wph
    @10
    cL
    crn
    wcel
    @16
    @6
    @42
    @22
    wph
    cP
    cG
    cI
    cL
    cD
    cE
    dfcgra2.p
    dfcgra2.i
    acopy.l
    dfcgra2.g
    dfcgra2.d
    dfcgra2.e
    wph
    cP
    cG
    cI
    cL
    cD
    cE
    cF
    dfcgra2.p
    dfcgra2.i
    acopy.l
    dfcgra2.g
    dfcgra2.d
    dfcgra2.e
    dfcgra2.f
    acopy.2
    ncolne1
    #
    tgelrnln
    ad4antr
    @18
    @0
    @10
    wcel
    @42
    @22
    @40
    ad2antrr
    wph
    cE
    @10
    wcel
    @16
    @6
    @42
    @22
    wph
    cP
    cD
    cE
    cG
    cI
    cL
    dfcgra2.p
    dfcgra2.i
    acopy.l
    dfcgra2.g
    dfcgra2.d
    dfcgra2.e
    @56
    tglinerflx2
    ad4antr
    tglinethru
    fveq2d
    breqd
    mpbird
    ex
    anim12d
    reximdva
    mpd
    wph
    vd
    cE
    cB
    cA
    cD
    cP
    cG
    cI
    @1
    c.mi
    dfcgra2.p
    dfcgra2.i
    @24
    dfcgra2.e
    dfcgra2.b
    dfcgra2.a
    dfcgra2.g
    dfcgra2.d
    dfcgra2.m
    @56
    wph
    cA
    cB
    @52
    necomd
    hlcgrex
    r19.29a
end

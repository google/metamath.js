include "cof.mm"
include "co.mm"
include "wcel.mm"
include "cgsu.mm"
include "wceq.mm"
include "cminusg.mm"
include "cfv.mm"
include "ccom.mm"
include "cplusg.mm"
include "cv.mm"
include "cmpt.mm"
include "wa.mm"
include "cbs.mm"
include "eqid.mm"
include "dprdff.mm"
include "ffvelrnda.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "dprddomcld.mm"
include "feqmptd.mm"
include "offval2.mm"
include "fvexd.mm"
include "wf1o.mm"
include "wf.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "cgrp.mm"
include "dprdgrp.mm"
include "syl.mm"
include "grpinvf1o.mm"
include "f1of.mm"
include "fveq2.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "dprdfinv.mm"
include "simpld.mm"
include "dprdfadd.mm"
include "eqeltrd.mm"
include "oveq2d.mm"
include "simprd.mm"
include "dprdssv.mm"
include "eldprdi.mm"
include "sseldi.mm"
include "eqtrd.mm"
include "jca.mm"

theorem dprdfsub
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.mi: class .-
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vx: setvar x
  let c.pl: class .+
  let vn: setvar n
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  let cN: class N
  let cX: class X
  assume eldprdi.0: |- .0. = ( 0g ` G )
  assume eldprdi.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume eldprdi.1: |- ( ph -> G dom DProd S )
  assume eldprdi.2: |- ( ph -> dom S = I )
  assume eldprdi.3: |- ( ph -> F e. W )
  assume dprdfadd.4: |- ( ph -> H e. W )
  assume dprdfsub.b: |- .- = ( -g ` G )

  disjoint F h
  disjoint H h
  disjoint h i
  disjoint G h
  disjoint G i
  disjoint I h
  disjoint I i
  disjoint .0. h
  disjoint S h
  disjoint S i
  disjoint .- k
  disjoint h k
  disjoint h x
  disjoint .+ h
  disjoint k x
  disjoint .+ k
  disjoint .+ x
  disjoint h n
  disjoint A h
  disjoint A n
  disjoint f h
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint h y
  disjoint k y
  disjoint F k
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint f i
  disjoint f n
  disjoint G f
  disjoint i k
  disjoint i n
  disjoint i x
  disjoint i y
  disjoint k n
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint I f
  disjoint I k
  disjoint I n
  disjoint I x
  disjoint I y
  disjoint N h
  disjoint N x
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint .0. k
  disjoint .0. n
  disjoint .0. x
  disjoint .0. y
  disjoint S f
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint W f
  disjoint X h
  disjoint X n
  assert |- ( ph -> ( ( F oF .- H ) e. W /\ ( G gsum ( F oF .- H ) ) = ( ( G gsum F ) .- ( G gsum H ) ) ) )

  proof
    wph
    cF
    cH
    c.mi
    cof
    co
    #
    cW
    wcel
    cG
    @0
    cgsu
    co
    #
    cG
    cF
    cgsu
    co
    #
    cG
    cH
    cgsu
    co
    #
    c.mi
    co
    #
    wceq
    wph
    @0
    cF
    cG
    cminusg
    cfv
    #
    cH
    ccom
    #
    cG
    cplusg
    cfv
    #
    cof
    co
    #
    cW
    wph
    vk
    cI
    vk
    cv
    #
    cF
    cfv
    #
    @9
    cH
    cfv
    #
    c.mi
    co
    #
    cmpt
    vk
    cI
    @10
    @11
    @5
    cfv
    #
    @7
    co
    #
    cmpt
    @0
    @8
    wph
    vk
    cI
    @12
    @14
    wph
    @9
    cI
    wcel
    wa
    #
    @10
    cG
    cbs
    cfv
    #
    wcel
    @11
    @16
    wcel
    @12
    @14
    wceq
    wph
    cI
    @16
    @9
    cF
    wph
    @16
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    @16
    eqid
    #
    dprdff
    #
    ffvelrnda
    #
    wph
    cI
    @16
    @9
    cH
    wph
    @16
    cS
    vh
    vi
    cH
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    dprdfadd.4
    @17
    dprdff
    #
    ffvelrnda
    #
    @16
    @7
    cG
    @5
    c.mi
    @10
    @11
    @17
    @7
    eqid
    #
    @5
    eqid
    #
    dprdfsub.b
    grpsubval
    syl2anc
    mpteq2dva
    wph
    vk
    cI
    @10
    @11
    c.mi
    cF
    cH
    cvv
    @16
    @16
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprddomcld
    #
    @19
    @21
    wph
    vk
    cI
    @16
    cF
    @18
    feqmptd
    #
    wph
    vk
    cI
    @16
    cH
    @20
    feqmptd
    #
    offval2
    wph
    vk
    cI
    @10
    @13
    @7
    cF
    @6
    cvv
    @16
    cvv
    @24
    @19
    @15
    @11
    @5
    fvexd
    @25
    wph
    vk
    vx
    cI
    @16
    @11
    vx
    cv
    #
    @5
    cfv
    @13
    cH
    @5
    @21
    @26
    wph
    vx
    @16
    @16
    @5
    wph
    @16
    @16
    @5
    wf1o
    @16
    @16
    @5
    wf
    wph
    @16
    cG
    @5
    @17
    @23
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    cG
    cgrp
    wcel
    eldprdi.1
    cS
    cG
    dprdgrp
    syl
    grpinvf1o
    @16
    @16
    @5
    f1of
    syl
    feqmptd
    @27
    @11
    @5
    fveq2
    fmptco
    offval2
    3eqtr4d
    #
    wph
    @8
    cW
    wcel
    #
    cG
    @8
    cgsu
    co
    #
    @2
    cG
    @6
    cgsu
    co
    #
    @7
    co
    #
    wceq
    #
    wph
    @7
    cS
    vh
    vi
    cF
    cG
    @6
    cI
    cW
    c.0
    eldprdi.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    wph
    @6
    cW
    wcel
    #
    @31
    @3
    @5
    cfv
    #
    wceq
    #
    wph
    cS
    vh
    vi
    cH
    cG
    cI
    @5
    cW
    c.0
    eldprdi.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    dprdfadd.4
    @23
    dprdfinv
    #
    simpld
    @22
    dprdfadd
    #
    simpld
    eqeltrd
    wph
    @1
    @30
    @4
    wph
    @0
    @8
    cG
    cgsu
    @28
    oveq2d
    wph
    @32
    @2
    @35
    @7
    co
    #
    @30
    @4
    wph
    @31
    @35
    @2
    @7
    wph
    @34
    @36
    @37
    simprd
    oveq2d
    wph
    @29
    @33
    @38
    simprd
    wph
    @2
    @16
    wcel
    @3
    @16
    wcel
    @4
    @39
    wceq
    wph
    cG
    cS
    cdprd
    co
    #
    @16
    @2
    @16
    cS
    cG
    @17
    dprdssv
    #
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    eldprdi.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    eldprdi
    sseldi
    wph
    @40
    @16
    @3
    @41
    wph
    cS
    vh
    vi
    cH
    cG
    cI
    cW
    c.0
    eldprdi.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    dprdfadd.4
    eldprdi
    sseldi
    @16
    @7
    cG
    @5
    c.mi
    @2
    @3
    @17
    @22
    @23
    dprdfsub.b
    grpsubval
    syl2anc
    3eqtr4d
    eqtrd
    jca
end

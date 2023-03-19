include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cgsu.mm"
include "co.mm"
include "csg.mm"
include "wfn.mm"
include "wb.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "dprdff.mm"
include "ffn.mm"
include "syl.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "cof.mm"
include "cmpt.mm"
include "wcel.mm"
include "dprdfsub.mm"
include "simpld.mm"
include "dprdfeq0.mm"
include "simprd.mm"
include "eqeq1d.mm"
include "cvv.mm"
include "dprddomcld.mm"
include "wa.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "ovex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "ax-mp.mm"
include "cgrp.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "dprdgrp.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "grpsubeq0.mm"
include "syl3anc.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "3bitr3d.mm"
include "dprdssv.mm"
include "eldprdi.mm"
include "sseldi.mm"
include "3bitr2rd.mm"

theorem dprdf11
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let c.mi: class .-
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
  assume dprdf11.4: |- ( ph -> H e. W )

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
  assert |- ( ph -> ( ( G gsum F ) = ( G gsum H ) <-> F = H ) )

  proof
    wph
    cF
    cH
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cH
    cfv
    #
    wceq
    #
    vx
    cI
    wral
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
    cG
    csg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @6
    @7
    wceq
    #
    wph
    cF
    cI
    wfn
    #
    cH
    cI
    wfn
    #
    @0
    @5
    wb
    wph
    cI
    cG
    cbs
    cfv
    #
    cF
    wf
    @12
    wph
    @14
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
    @14
    eqid
    #
    dprdff
    #
    cI
    @14
    cF
    ffn
    syl
    wph
    cI
    @14
    cH
    wf
    @13
    wph
    @14
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
    dprdf11.4
    @15
    dprdff
    #
    cI
    @14
    cH
    ffn
    syl
    vx
    cI
    cF
    cH
    eqfnfv
    syl2anc
    wph
    cG
    cF
    cH
    @8
    cof
    co
    #
    cgsu
    co
    #
    c.0
    wceq
    @18
    vx
    cI
    c.0
    cmpt
    #
    wceq
    #
    @10
    @5
    wph
    vx
    cS
    vh
    vi
    @18
    cG
    cI
    cW
    c.0
    eldprdi.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    wph
    @18
    cW
    wcel
    #
    @19
    @9
    wceq
    #
    wph
    cS
    vh
    vi
    cF
    cG
    cH
    cI
    @8
    cW
    c.0
    eldprdi.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    dprdf11.4
    @8
    eqid
    #
    dprdfsub
    #
    simpld
    dprdfeq0
    wph
    @19
    @9
    c.0
    wph
    @22
    @23
    @25
    simprd
    eqeq1d
    wph
    @21
    vx
    cI
    @2
    @3
    @8
    co
    #
    cmpt
    #
    @20
    wceq
    #
    @5
    wph
    @18
    @27
    @20
    wph
    vx
    cI
    @2
    @3
    @8
    cF
    cH
    cvv
    cvv
    cvv
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprddomcld
    wph
    @1
    cI
    wcel
    #
    wa
    #
    @1
    cF
    fvexd
    @30
    @1
    cH
    fvexd
    wph
    vx
    cI
    @14
    cF
    @16
    feqmptd
    wph
    vx
    cI
    @14
    cH
    @17
    feqmptd
    offval2
    eqeq1d
    @28
    @26
    c.0
    wceq
    #
    vx
    cI
    wral
    #
    wph
    @5
    @26
    cvv
    wcel
    #
    vx
    cI
    wral
    @28
    @32
    wb
    @33
    vx
    cI
    @2
    @3
    @8
    ovex
    rgenw
    vx
    cI
    @26
    c.0
    cvv
    mpteqb
    ax-mp
    wph
    @31
    @4
    vx
    cI
    @30
    cG
    cgrp
    wcel
    #
    @2
    @14
    wcel
    @3
    @14
    wcel
    @31
    @4
    wb
    wph
    @34
    @29
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    @34
    eldprdi.1
    cS
    cG
    dprdgrp
    syl
    #
    adantr
    wph
    cI
    @14
    @1
    cF
    @16
    ffvelrnda
    wph
    cI
    @14
    @1
    cH
    @17
    ffvelrnda
    @14
    cG
    @8
    @2
    @3
    c.0
    @15
    eldprdi.0
    @24
    grpsubeq0
    syl3anc
    ralbidva
    syl5bb
    bitrd
    3bitr3d
    wph
    @34
    @6
    @14
    wcel
    @7
    @14
    wcel
    @10
    @11
    wb
    @35
    wph
    cG
    cS
    cdprd
    co
    #
    @14
    @6
    @14
    cS
    cG
    @15
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
    @36
    @14
    @7
    @37
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
    dprdf11.4
    eldprdi
    sseldi
    @14
    cG
    @8
    @6
    @7
    c.0
    @15
    eldprdi.0
    @24
    grpsubeq0
    syl3anc
    3bitr2rd
end

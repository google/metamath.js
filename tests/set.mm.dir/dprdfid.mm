include "wcel.mm"
include "cgsu.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "cfv.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "wn.mm"
include "csubg.mm"
include "dprdf2.mm"
include "ffvelrnda.mm"
include "subg0cl.mm"
include "syl.mm"
include "adantr.mm"
include "ifclda.mm"
include "cvv.mm"
include "dprddomcld.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "eqid.mm"
include "sniffsupp.mm"
include "dprdwd.mm"
include "syl5eqel.mm"
include "cbs.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "cgrp.mm"
include "cmnd.mm"
include "dprdgrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "dprdff.mm"
include "csupp.mm"
include "csn.mm"
include "oveq1i.mm"
include "cdif.mm"
include "wne.mm"
include "eldifsni.mm"
include "adantl.mm"
include "ifnefalse.mm"
include "suppss2.mm"
include "syl5eqss.mm"
include "gsumpt.mm"
include "iftrue.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "jca.mm"

theorem dprdfid
  let wph: wff ph
  let cA: class A
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let c.mi: class .-
  let vk: setvar k
  let vx: setvar x
  let c.pl: class .+
  let vf: setvar f
  let vy: setvar y
  let cH: class H
  let cN: class N
  assume eldprdi.0: |- .0. = ( 0g ` G )
  assume eldprdi.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume eldprdi.1: |- ( ph -> G dom DProd S )
  assume eldprdi.2: |- ( ph -> dom S = I )
  assume dprdfid.3: |- ( ph -> X e. I )
  assume dprdfid.4: |- ( ph -> A e. ( S ` X ) )
  assume dprdfid.f: |- F = ( n e. I |-> if ( n = X , A , .0. ) )

  disjoint h n
  disjoint A h
  disjoint A n
  disjoint F h
  disjoint h i
  disjoint G h
  disjoint i n
  disjoint G i
  disjoint G n
  disjoint I h
  disjoint I i
  disjoint I n
  disjoint n ph
  disjoint .0. h
  disjoint .0. n
  disjoint S h
  disjoint S i
  disjoint S n
  disjoint X h
  disjoint X n
  disjoint .- k
  disjoint h k
  disjoint h x
  disjoint .+ h
  disjoint k x
  disjoint .+ k
  disjoint .+ x
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
  disjoint H h
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint f i
  disjoint f n
  disjoint G f
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k n
  disjoint G k
  disjoint n x
  disjoint n y
  disjoint G x
  disjoint G y
  disjoint I f
  disjoint I k
  disjoint I x
  disjoint I y
  disjoint N h
  disjoint N x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint .0. k
  disjoint .0. x
  disjoint .0. y
  disjoint S f
  disjoint S x
  disjoint S y
  disjoint W f
  assert |- ( ph -> ( F e. W /\ ( G gsum F ) = A ) )

  proof
    wph
    cF
    cW
    wcel
    cG
    cF
    cgsu
    co
    #
    cA
    wceq
    wph
    cF
    vn
    cI
    vn
    cv
    #
    cX
    wceq
    #
    cA
    c.0
    cif
    #
    cmpt
    #
    cW
    dprdfid.f
    wph
    vn
    @3
    cS
    vh
    vi
    cG
    cI
    cW
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    wph
    @1
    cI
    wcel
    #
    wa
    #
    @2
    cA
    c.0
    @1
    cS
    cfv
    #
    @6
    @2
    wa
    #
    cA
    cX
    cS
    cfv
    #
    @7
    wph
    cA
    @9
    wcel
    #
    @5
    @2
    dprdfid.4
    ad2antrr
    @8
    @1
    cX
    cS
    @6
    @2
    simpr
    fveq2d
    eleqtrrd
    @6
    c.0
    @7
    wcel
    #
    @2
    wn
    @6
    @7
    cG
    csubg
    cfv
    #
    wcel
    @11
    wph
    cI
    @12
    @1
    cS
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprdf2
    ffvelrnda
    @7
    cG
    c.0
    eldprdi.0
    subg0cl
    syl
    adantr
    ifclda
    wph
    vn
    cA
    @4
    cI
    cvv
    cvv
    cX
    c.0
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprddomcld
    #
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    eldprdi.0
    cG
    c0g
    fvex
    eqeltri
    a1i
    @4
    eqid
    sniffsupp
    dprdwd
    syl5eqel
    #
    wph
    @0
    cX
    cF
    cfv
    #
    cA
    wph
    cI
    cG
    cbs
    cfv
    #
    cF
    cG
    cvv
    cX
    c.0
    @16
    eqid
    #
    eldprdi.0
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    eldprdi.1
    cS
    cG
    dprdgrp
    cG
    grpmnd
    3syl
    @13
    dprdfid.3
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
    @14
    @17
    dprdff
    wph
    cF
    c.0
    csupp
    co
    @4
    c.0
    csupp
    co
    cX
    csn
    #
    cF
    @4
    c.0
    csupp
    dprdfid.f
    oveq1i
    wph
    cI
    @3
    vn
    cvv
    @18
    c.0
    wph
    @1
    cI
    @18
    cdif
    wcel
    #
    wa
    @1
    cX
    wne
    #
    @3
    c.0
    wceq
    @19
    @20
    wph
    @1
    cI
    cX
    eldifsni
    adantl
    @1
    cX
    cA
    c.0
    ifnefalse
    syl
    @13
    suppss2
    syl5eqss
    gsumpt
    wph
    cX
    cI
    wcel
    @10
    @15
    cA
    wceq
    dprdfid.3
    dprdfid.4
    vn
    cX
    @3
    cA
    cI
    @9
    cF
    @2
    cA
    c.0
    iftrue
    dprdfid.f
    fvmptg
    syl2anc
    eqtrd
    jca
end

include "ccom.mm"
include "wcel.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cmpt.mm"
include "cbs.mm"
include "wf.mm"
include "cgrp.mm"
include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "dprdgrp.mm"
include "syl.mm"
include "eqid.mm"
include "grpinvf.mm"
include "dprdff.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "wa.mm"
include "csubg.mm"
include "dprdf2.mm"
include "ffvelrnda.mm"
include "dprdfcl.mm"
include "subginvcl.mm"
include "cvv.mm"
include "wfun.mm"
include "cfsupp.mm"
include "csupp.mm"
include "wss.mm"
include "dprddomcld.mm"
include "mptexg.mm"
include "funmpt.mm"
include "a1i.mm"
include "dprdffsupp.mm"
include "cdif.mm"
include "ssid.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "fveq2d.mm"
include "grpinvid.mm"
include "adantr.mm"
include "eqtrd.mm"
include "suppss2.mm"
include "fsuppsssupp.mm"
include "syl22anc.mm"
include "dprdwd.mm"
include "eqeltrd.mm"
include "ccntz.mm"
include "dprdfcntz.mm"
include "gsumzinv.mm"
include "jca.mm"

theorem dprdfinv
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
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
  let cH: class H
  let cX: class X
  assume eldprdi.0: |- .0. = ( 0g ` G )
  assume eldprdi.w: |- W = { h e. X_ i e. I ( S ` i ) | h finSupp .0. }
  assume eldprdi.1: |- ( ph -> G dom DProd S )
  assume eldprdi.2: |- ( ph -> dom S = I )
  assume eldprdi.3: |- ( ph -> F e. W )
  assume dprdfinv.b: |- N = ( invg ` G )

  disjoint F h
  disjoint h i
  disjoint G h
  disjoint G i
  disjoint I h
  disjoint I i
  disjoint N h
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
  disjoint H h
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
  assert |- ( ph -> ( ( N o. F ) e. W /\ ( G gsum ( N o. F ) ) = ( N ` ( G gsum F ) ) ) )

  proof
    wph
    cN
    cF
    ccom
    #
    cW
    wcel
    cG
    @0
    cgsu
    co
    cG
    cF
    cgsu
    co
    cN
    cfv
    wceq
    wph
    @0
    vx
    cI
    vx
    cv
    #
    cF
    cfv
    #
    cN
    cfv
    #
    cmpt
    #
    cW
    wph
    cG
    cbs
    cfv
    #
    @5
    cN
    wf
    #
    cI
    @5
    cF
    wf
    @0
    @4
    wceq
    wph
    cG
    cgrp
    wcel
    #
    @6
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    @7
    eldprdi.1
    cS
    cG
    dprdgrp
    syl
    #
    @5
    cG
    cN
    @5
    eqid
    #
    dprdfinv.b
    grpinvf
    syl
    wph
    @5
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
    @9
    dprdff
    #
    vx
    cN
    cF
    cI
    @5
    @5
    fcompt
    syl2anc
    wph
    vx
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
    wa
    @1
    cS
    cfv
    #
    cG
    csubg
    cfv
    #
    wcel
    @2
    @11
    wcel
    @3
    @11
    wcel
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
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    @1
    c.0
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    dprdfcl
    @11
    cG
    cN
    @2
    dprdfinv.b
    subginvcl
    syl2anc
    wph
    @4
    cvv
    wcel
    #
    @4
    wfun
    #
    cF
    c.0
    cfsupp
    wbr
    @4
    c.0
    csupp
    co
    cF
    c.0
    csupp
    co
    #
    wss
    @4
    c.0
    cfsupp
    wbr
    wph
    cI
    cvv
    wcel
    @13
    wph
    cS
    cG
    cI
    eldprdi.1
    eldprdi.2
    dprddomcld
    #
    vx
    cI
    @3
    cvv
    mptexg
    syl
    @14
    wph
    vx
    cI
    @3
    funmpt
    a1i
    wph
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
    dprdffsupp
    #
    wph
    cI
    @3
    vx
    cvv
    @15
    c.0
    wph
    @1
    cI
    @15
    cdif
    wcel
    #
    wa
    #
    @3
    c.0
    cN
    cfv
    #
    c.0
    @19
    @2
    c.0
    cN
    wph
    cI
    @5
    cvv
    cF
    cvv
    @15
    @1
    c.0
    @10
    @15
    @15
    wss
    wph
    @15
    ssid
    a1i
    @16
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
    suppssr
    fveq2d
    wph
    @20
    c.0
    wceq
    #
    @18
    wph
    @7
    @21
    @8
    cG
    cN
    c.0
    eldprdi.0
    dprdfinv.b
    grpinvid
    syl
    adantr
    eqtrd
    @16
    suppss2
    cF
    @4
    cvv
    c.0
    fsuppsssupp
    syl22anc
    dprdwd
    eqeltrd
    wph
    cI
    @5
    cF
    cG
    cN
    cvv
    c.0
    cG
    ccntz
    cfv
    #
    @9
    eldprdi.0
    @22
    eqid
    #
    dprdfinv.b
    @8
    @16
    @10
    wph
    cS
    vh
    vi
    cF
    cG
    cI
    cW
    c.0
    @22
    eldprdi.w
    eldprdi.1
    eldprdi.2
    eldprdi.3
    @23
    dprdfcntz
    @17
    gsumzinv
    jca
end

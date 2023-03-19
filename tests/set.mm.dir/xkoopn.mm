include "cv.mm"
include "cima.mm"
include "wss.mm"
include "ccn.mm"
include "co.mm"
include "crab.mm"
include "crest.mm"
include "ccmp.mm"
include "wcel.mm"
include "cpw.mm"
include "cmpt2.mm"
include "crn.mm"
include "cfi.mm"
include "cfv.mm"
include "ctg.mm"
include "cxko.mm"
include "cvv.mm"
include "ovex.mm"
include "pwex.mm"
include "cxp.mm"
include "wf.mm"
include "eqid.mm"
include "xkotf.mm"
include "frn.mm"
include "ax-mp.mm"
include "ssexi.mm"
include "ssfii.mm"
include "fvex.mm"
include "bastg.mm"
include "sstri.mm"
include "wceq.mm"
include "wrex.mm"
include "ctop.mm"
include "wb.mm"
include "topopn.mm"
include "elpw2g.mm"
include "3syl.mm"
include "mpbird.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "eqidd.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "sseq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "rabex.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "rnmpt2.mm"
include "elab2.mm"
include "sylibr.mm"
include "sseldi.mm"
include "xkoval.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"

theorem xkoopn
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let cX: class X
  let vk: setvar k
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume xkoopn.x: |- X = U. R
  assume xkoopn.r: |- ( ph -> R e. Top )
  assume xkoopn.s: |- ( ph -> S e. Top )
  assume xkoopn.a: |- ( ph -> A C_ X )
  assume xkoopn.c: |- ( ph -> ( R |`t A ) e. Comp )
  assume xkoopn.u: |- ( ph -> U e. S )

  disjoint A f
  disjoint R f
  disjoint S f
  disjoint U f
  disjoint f k
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint R k
  disjoint R v
  disjoint R x
  disjoint R y
  disjoint S k
  disjoint S v
  disjoint S x
  disjoint S y
  disjoint U k
  disjoint U v
  disjoint U y
  disjoint X k
  disjoint X v
  disjoint X x
  disjoint X y
  assert |- ( ph -> { f e. ( R Cn S ) | ( f " A ) C_ U } e. ( S ^ko R ) )

  proof
    wph
    vf
    cv
    #
    cA
    cima
    #
    cU
    wss
    #
    vf
    cR
    cS
    ccn
    co
    #
    crab
    #
    vk
    vv
    cR
    vx
    cv
    #
    crest
    co
    #
    ccmp
    wcel
    #
    vx
    cX
    cpw
    #
    crab
    #
    cS
    @0
    vk
    cv
    #
    cima
    #
    vv
    cv
    #
    wss
    #
    vf
    @3
    crab
    #
    cmpt2
    #
    crn
    #
    cfi
    cfv
    #
    ctg
    cfv
    #
    cS
    cR
    cxko
    co
    #
    wph
    @16
    @18
    @4
    @16
    @17
    @18
    @16
    cvv
    wcel
    @16
    @17
    wss
    @16
    @3
    cpw
    #
    @3
    cR
    cS
    ccn
    ovex
    #
    pwex
    @9
    cS
    cxp
    #
    @20
    @15
    wf
    @16
    @20
    wss
    vx
    vv
    cR
    cS
    @15
    vf
    vk
    @9
    cX
    xkoopn.x
    @9
    eqid
    #
    @15
    eqid
    #
    xkotf
    @22
    @20
    @15
    frn
    ax-mp
    ssexi
    @16
    cvv
    ssfii
    ax-mp
    @17
    cvv
    wcel
    @17
    @18
    wss
    @16
    cfi
    fvex
    @17
    cvv
    bastg
    ax-mp
    sstri
    wph
    @4
    @14
    wceq
    #
    vv
    cS
    wrex
    vk
    @9
    wrex
    #
    @4
    @16
    wcel
    wph
    cA
    @9
    wcel
    #
    cU
    cS
    wcel
    @4
    @4
    wceq
    #
    @26
    wph
    cA
    @8
    wcel
    #
    cR
    cA
    crest
    co
    #
    ccmp
    wcel
    #
    @27
    wph
    @29
    cA
    cX
    wss
    #
    xkoopn.a
    wph
    cR
    ctop
    wcel
    #
    cX
    cR
    wcel
    @29
    @32
    wb
    xkoopn.r
    cR
    cX
    xkoopn.x
    topopn
    cA
    cX
    cR
    elpw2g
    3syl
    mpbird
    xkoopn.c
    @7
    @31
    vx
    cA
    @8
    @5
    cA
    wceq
    @6
    @30
    ccmp
    @5
    cA
    cR
    crest
    oveq2
    eleq1d
    elrab
    sylanbrc
    xkoopn.u
    wph
    @4
    eqidd
    @25
    @28
    @4
    @1
    @12
    wss
    #
    vf
    @3
    crab
    #
    wceq
    vk
    vv
    cA
    cU
    @9
    cS
    @10
    cA
    wceq
    #
    @14
    @35
    @4
    @36
    @13
    @34
    vf
    @3
    @36
    @11
    @1
    @12
    @10
    cA
    @0
    imaeq2
    sseq1d
    rabbidv
    eqeq2d
    @12
    cU
    wceq
    #
    @35
    @4
    @4
    @37
    @34
    @2
    vf
    @3
    @12
    cU
    @1
    sseq2
    rabbidv
    eqeq2d
    rspc2ev
    syl3anc
    vy
    cv
    #
    @14
    wceq
    #
    vv
    cS
    wrex
    vk
    @9
    wrex
    @26
    vy
    @4
    @16
    @2
    vf
    @3
    @21
    rabex
    @38
    @4
    wceq
    @39
    @25
    vk
    vv
    @9
    cS
    @38
    @4
    @14
    eqeq1
    2rexbidv
    vk
    vv
    vy
    @9
    cS
    @14
    @15
    @24
    rnmpt2
    elab2
    sylibr
    sseldi
    wph
    @33
    cS
    ctop
    wcel
    @19
    @18
    wceq
    xkoopn.r
    xkoopn.s
    vx
    vv
    cR
    cS
    @15
    vf
    vk
    @9
    cX
    xkoopn.x
    @23
    @24
    xkoval
    syl2anc
    eleqtrrd
end

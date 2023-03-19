include "cof.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "fsuppimpd.mm"
include "lcomf.mm"
include "cv.mm"
include "cdif.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "eldifi.mm"
include "wfn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "sylan2.mm"
include "cvv.mm"
include "ssid.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppssr.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ffvelrnda.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "ssfi.mm"
include "wfun.mm"
include "wb.mm"
include "inidm.mm"
include "offn.mm"
include "fnfun.mm"
include "ovexd.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem lcomfsupp
  let wph: wff ph
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume lcomf.f: |- F = ( Scalar ` W )
  assume lcomf.k: |- K = ( Base ` F )
  assume lcomf.s: |- .x. = ( .s ` W )
  assume lcomf.b: |- B = ( Base ` W )
  assume lcomf.w: |- ( ph -> W e. LMod )
  assume lcomf.g: |- ( ph -> G : I --> K )
  assume lcomf.h: |- ( ph -> H : I --> B )
  assume lcomf.i: |- ( ph -> I e. V )
  assume lcomfsupp.z: |- .0. = ( 0g ` W )
  assume lcomfsupp.y: |- Y = ( 0g ` F )
  assume lcomfsupp.j: |- ( ph -> G finSupp Y )


  assert |- ( ph -> ( G oF .x. H ) finSupp .0. )

  proof
    wph
    cG
    cH
    c.x
    cof
    #
    co
    #
    c.0
    cfsupp
    wbr
    #
    @1
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    cG
    cY
    csupp
    co
    #
    cfn
    wcel
    @3
    @5
    wss
    @4
    wph
    cG
    cY
    lcomfsupp.j
    fsuppimpd
    wph
    cI
    cB
    vx
    @1
    @5
    c.0
    wph
    cB
    c.x
    cF
    cG
    cH
    cI
    cK
    cV
    cW
    lcomf.f
    lcomf.k
    lcomf.s
    lcomf.b
    lcomf.w
    lcomf.g
    lcomf.h
    lcomf.i
    lcomf
    wph
    vx
    cv
    #
    cI
    @5
    cdif
    wcel
    #
    wa
    #
    @6
    @1
    cfv
    #
    @6
    cG
    cfv
    #
    @6
    cH
    cfv
    #
    c.x
    co
    #
    cY
    @11
    c.x
    co
    #
    c.0
    @7
    wph
    @6
    cI
    wcel
    #
    @9
    @12
    wceq
    #
    @6
    cI
    @5
    eldifi
    #
    wph
    @14
    wa
    #
    cG
    cI
    wfn
    #
    cH
    cI
    wfn
    #
    cI
    cV
    wcel
    #
    @14
    @15
    wph
    @18
    @14
    wph
    cI
    cK
    cG
    wf
    @18
    lcomf.g
    cI
    cK
    cG
    ffn
    syl
    #
    adantr
    wph
    @19
    @14
    wph
    cI
    cB
    cH
    wf
    @19
    lcomf.h
    cI
    cB
    cH
    ffn
    syl
    #
    adantr
    wph
    @20
    @14
    lcomf.i
    adantr
    wph
    @14
    simpr
    cI
    c.x
    cG
    cH
    cV
    @6
    fnfvof
    syl22anc
    sylan2
    @8
    @10
    cY
    @11
    c.x
    wph
    cI
    cK
    cvv
    cG
    cV
    @5
    @6
    cY
    lcomf.g
    @5
    @5
    wss
    wph
    @5
    ssid
    a1i
    lcomf.i
    cY
    cvv
    wcel
    wph
    cY
    cF
    c0g
    cfv
    cvv
    lcomfsupp.y
    cF
    c0g
    fvex
    eqeltri
    a1i
    suppssr
    oveq1d
    @7
    wph
    @14
    @13
    c.0
    wceq
    #
    @16
    @17
    cW
    clmod
    wcel
    #
    @11
    cB
    wcel
    @23
    wph
    @24
    @14
    lcomf.w
    adantr
    wph
    cI
    cB
    @6
    cH
    lcomf.h
    ffvelrnda
    c.x
    cF
    cY
    cB
    cW
    @11
    c.0
    lcomf.b
    lcomf.f
    lcomf.s
    lcomfsupp.y
    lcomfsupp.z
    lmod0vs
    syl2anc
    sylan2
    3eqtrd
    suppss
    @5
    @3
    ssfi
    syl2anc
    wph
    @1
    wfun
    #
    @1
    cvv
    wcel
    c.0
    cvv
    wcel
    #
    @2
    @4
    wb
    wph
    @1
    cI
    wfn
    @25
    wph
    cI
    cI
    c.x
    cI
    cG
    cH
    cV
    cV
    @21
    @22
    lcomf.i
    lcomf.i
    cI
    inidm
    offn
    cI
    @1
    fnfun
    syl
    wph
    cG
    cH
    @0
    ovexd
    @26
    wph
    c.0
    cW
    c0g
    cfv
    cvv
    lcomfsupp.z
    cW
    c0g
    fvex
    eqeltri
    a1i
    @1
    cvv
    cvv
    c.0
    funisfsupp
    syl3anc
    mpbird
end

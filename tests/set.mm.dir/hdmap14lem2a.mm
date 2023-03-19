include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "c0g.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "csn.mm"
include "cdif.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "difss.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "eqid.mm"
include "simpr.mm"
include "hdmap14lem1a.mm"
include "eqcomd.mm"
include "wb.mm"
include "cbs.mm"
include "lcdlvec.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "hdmapcl.mm"
include "lspsneq.mm"
include "mpbid.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "lcdlmod.mm"
include "lmod0cl.mm"
include "syl.mm"
include "hdmapval0.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "pm2.61ne.mm"

theorem hdmap14lem2a
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let cX: class X
  assume hdmap14lem1a.h: |- H = ( LHyp ` K )
  assume hdmap14lem1a.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem1a.v: |- V = ( Base ` U )
  assume hdmap14lem1a.t: |- .x. = ( .s ` U )
  assume hdmap14lem1a.r: |- R = ( Scalar ` U )
  assume hdmap14lem1a.b: |- B = ( Base ` R )
  assume hdmap14lem1a.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem2a.e: |- .xb = ( .s ` C )
  assume hdmap14lem1a.l: |- L = ( LSpan ` C )
  assume hdmap14lem2a.p: |- P = ( Scalar ` C )
  assume hdmap14lem2a.a: |- A = ( Base ` P )
  assume hdmap14lem1a.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem1a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem3a.x: |- ( ph -> X e. V )
  assume hdmap14lem1a.f: |- ( ph -> F e. B )

  disjoint A g
  disjoint F g
  disjoint P g
  disjoint R g
  disjoint .x. g
  disjoint .xb g
  disjoint S g
  disjoint X g
  assert |- ( ph -> E. g e. A ( S ` ( F .x. X ) ) = ( g .xb ( S ` X ) ) )

  proof
    wph
    cF
    cX
    c.x
    co
    #
    cS
    cfv
    #
    vg
    cv
    #
    cX
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    vg
    cA
    wrex
    #
    cR
    c0g
    cfv
    #
    cX
    c.x
    co
    #
    cS
    cfv
    #
    @4
    wceq
    #
    vg
    cA
    wrex
    #
    cF
    @7
    cF
    @7
    wceq
    #
    @5
    @10
    vg
    cA
    @12
    @1
    @9
    @4
    @12
    @0
    @8
    cS
    cF
    @7
    cX
    c.x
    oveq1
    fveq2d
    eqeq1d
    rexbidv
    cA
    cP
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    cA
    wss
    wph
    cF
    @7
    wne
    #
    wa
    #
    @5
    vg
    @15
    wrex
    #
    @6
    cA
    @14
    difss
    @17
    @1
    csn
    cL
    cfv
    #
    @3
    csn
    cL
    cfv
    #
    wceq
    #
    @18
    @17
    @20
    @19
    @17
    cA
    cB
    cC
    cP
    cR
    cS
    c.xb
    c.x
    cU
    cF
    cH
    cK
    cL
    cV
    cW
    cX
    @7
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.v
    hdmap14lem1a.t
    hdmap14lem1a.r
    hdmap14lem1a.b
    hdmap14lem1a.c
    hdmap14lem2a.e
    hdmap14lem1a.l
    hdmap14lem2a.p
    hdmap14lem2a.a
    hdmap14lem1a.s
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @16
    hdmap14lem1a.k
    adantr
    wph
    cX
    cV
    wcel
    #
    @16
    hdmap14lem3a.x
    adantr
    wph
    cF
    cB
    wcel
    #
    @16
    hdmap14lem1a.f
    adantr
    @7
    eqid
    #
    wph
    @16
    simpr
    hdmap14lem1a
    eqcomd
    wph
    @21
    @18
    wb
    @16
    wph
    cP
    c.xb
    vg
    cA
    cL
    cC
    cbs
    cfv
    #
    cC
    @1
    @3
    @13
    @25
    eqid
    #
    hdmap14lem2a.p
    hdmap14lem2a.a
    @13
    eqid
    #
    hdmap14lem2a.e
    hdmap14lem1a.l
    wph
    cC
    cH
    cK
    cW
    hdmap14lem1a.h
    hdmap14lem1a.c
    hdmap14lem1a.k
    lcdlvec
    wph
    cC
    @25
    cS
    @0
    cU
    cH
    cK
    cV
    cW
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.v
    hdmap14lem1a.c
    @26
    hdmap14lem1a.s
    hdmap14lem1a.k
    wph
    cU
    clmod
    wcel
    #
    @23
    @22
    @0
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.k
    dvhlmod
    #
    hdmap14lem1a.f
    hdmap14lem3a.x
    cF
    c.x
    cR
    cB
    cV
    cU
    cX
    hdmap14lem1a.v
    hdmap14lem1a.r
    hdmap14lem1a.t
    hdmap14lem1a.b
    lmodvscl
    syl3anc
    hdmapcl
    wph
    cC
    @25
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmap14lem1a.h
    hdmap14lem1a.u
    hdmap14lem1a.v
    hdmap14lem1a.c
    @26
    hdmap14lem1a.s
    hdmap14lem1a.k
    hdmap14lem3a.x
    hdmapcl
    #
    lspsneq
    adantr
    mpbid
    @5
    vg
    @15
    cA
    ssrexv
    mpsyl
    wph
    @13
    cA
    wcel
    #
    @9
    @13
    @3
    c.xb
    co
    #
    wceq
    #
    @11
    wph
    cC
    clmod
    wcel
    #
    @31
    wph
    cC
    cH
    cK
    cW
    hdmap14lem1a.h
    hdmap14lem1a.c
    hdmap14lem1a.k
    lcdlmod
    #
    cP
    cA
    cC
    @13
    hdmap14lem2a.p
    hdmap14lem2a.a
    @27
    lmod0cl
    syl
    wph
    cU
    c0g
    cfv
    #
    cS
    cfv
    cC
    c0g
    cfv
    #
    @9
    @32
    wph
    cC
    @37
    cS
    cU
    cH
    cK
    cW
    @36
    hdmap14lem1a.h
    hdmap14lem1a.u
    @36
    eqid
    #
    hdmap14lem1a.c
    @37
    eqid
    #
    hdmap14lem1a.s
    hdmap14lem1a.k
    hdmapval0
    wph
    @8
    @36
    cS
    wph
    @28
    @22
    @8
    @36
    wceq
    @29
    hdmap14lem3a.x
    c.x
    cR
    @7
    cV
    cU
    cX
    @36
    hdmap14lem1a.v
    hdmap14lem1a.r
    hdmap14lem1a.t
    @24
    @38
    lmod0vs
    syl2anc
    fveq2d
    wph
    @34
    @3
    @25
    wcel
    @32
    @37
    wceq
    @35
    @30
    c.xb
    cP
    @13
    @25
    cC
    @3
    @37
    @26
    hdmap14lem2a.p
    hdmap14lem2a.e
    @27
    @39
    lmod0vs
    syl2anc
    3eqtr4d
    @10
    @33
    vg
    @13
    cA
    @2
    @13
    wceq
    @4
    @32
    @9
    @2
    @13
    @3
    c.xb
    oveq1
    eqeq2d
    rspcev
    syl2anc
    pm2.61ne
end

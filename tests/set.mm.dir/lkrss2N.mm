include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wpss.mm"
include "wo.mm"
include "sspss.mm"
include "c0g.mm"
include "wne.mm"
include "wa.mm"
include "eqid.mm"
include "lkrpssN.mm"
include "wcel.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmod0cl.mm"
include "adantr.mm"
include "simpr.mm"
include "ldual0vs.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "adantld.mm"
include "sylbid.mm"
include "imp.mm"
include "eqlkr4.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "wi.mm"
include "lkrss.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "impbida.mm"

theorem lkrss2N
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vr: setvar r
  assume lkrss2.s: |- S = ( Scalar ` W )
  assume lkrss2.r: |- R = ( Base ` S )
  assume lkrss2.f: |- F = ( LFnl ` W )
  assume lkrss2.k: |- K = ( LKer ` W )
  assume lkrss2.d: |- D = ( LDual ` W )
  assume lkrss2.t: |- .x. = ( .s ` D )
  assume lkrss2.w: |- ( ph -> W e. LVec )
  assume lkrss2.g: |- ( ph -> G e. F )
  assume lkrss2.h: |- ( ph -> H e. F )

  disjoint F r
  disjoint G r
  disjoint H r
  disjoint K r
  disjoint R r
  disjoint S r
  disjoint W r
  disjoint ph r
  disjoint .x. r
  assert |- ( ph -> ( ( K ` G ) C_ ( K ` H ) <-> E. r e. R H = ( r .x. G ) ) )

  proof
    wph
    cG
    cK
    cfv
    #
    cH
    cK
    cfv
    #
    wss
    #
    cH
    vr
    cv
    #
    cG
    c.x
    co
    #
    wceq
    #
    vr
    cR
    wrex
    #
    @2
    wph
    @0
    @1
    wpss
    #
    @0
    @1
    wceq
    #
    wo
    @6
    @0
    @1
    sspss
    wph
    @7
    @6
    @8
    wph
    @7
    @6
    wph
    @7
    cG
    cD
    c0g
    cfv
    #
    wne
    #
    cH
    @9
    wceq
    #
    wa
    @6
    wph
    cD
    cF
    cG
    cH
    cK
    cW
    @9
    lkrss2.f
    lkrss2.k
    lkrss2.d
    @9
    eqid
    #
    lkrss2.w
    lkrss2.g
    lkrss2.h
    lkrpssN
    wph
    @11
    @6
    @10
    wph
    @11
    @6
    wph
    @11
    wa
    #
    cS
    c0g
    cfv
    #
    cR
    wcel
    #
    cH
    @14
    cG
    c.x
    co
    #
    wceq
    #
    @6
    wph
    @15
    @11
    wph
    cW
    clmod
    wcel
    #
    @15
    wph
    cW
    clvec
    wcel
    #
    @18
    lkrss2.w
    cW
    lveclmod
    syl
    #
    cS
    cR
    cW
    @14
    lkrss2.s
    lkrss2.r
    @14
    eqid
    #
    lmod0cl
    syl
    adantr
    @13
    cH
    @9
    @16
    wph
    @11
    simpr
    wph
    @16
    @9
    wceq
    @11
    wph
    cD
    cS
    c.x
    cF
    cG
    @9
    cW
    @14
    lkrss2.f
    lkrss2.s
    @21
    lkrss2.d
    lkrss2.t
    @12
    @20
    lkrss2.g
    ldual0vs
    adantr
    eqtr4d
    @5
    @17
    vr
    @14
    cR
    @3
    @14
    wceq
    @4
    @16
    cH
    @3
    @14
    cG
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    ex
    adantld
    sylbid
    imp
    wph
    @8
    wa
    cD
    cR
    cS
    c.x
    cF
    cG
    cH
    cK
    cW
    vr
    lkrss2.s
    lkrss2.r
    lkrss2.f
    lkrss2.k
    lkrss2.d
    lkrss2.t
    wph
    @19
    @8
    lkrss2.w
    adantr
    wph
    cG
    cF
    wcel
    #
    @8
    lkrss2.g
    adantr
    wph
    cH
    cF
    wcel
    @8
    lkrss2.h
    adantr
    wph
    @8
    simpr
    eqlkr4
    jaodan
    sylan2b
    wph
    @6
    @2
    wph
    @5
    @2
    vr
    cR
    wph
    @3
    cR
    wcel
    #
    @0
    @4
    cK
    cfv
    #
    wss
    #
    @5
    @2
    wi
    wph
    @23
    @25
    wph
    @23
    wa
    cD
    cS
    c.x
    cF
    cG
    cR
    cK
    cW
    @3
    lkrss2.s
    lkrss2.r
    lkrss2.f
    lkrss2.k
    lkrss2.d
    lkrss2.t
    wph
    @19
    @23
    lkrss2.w
    adantr
    wph
    @22
    @23
    lkrss2.g
    adantr
    wph
    @23
    simpr
    lkrss
    ex
    @5
    @2
    @25
    @5
    @1
    @24
    @0
    cH
    @4
    cK
    fveq2
    sseq2d
    biimprcd
    syl6
    rexlimdv
    imp
    impbida
end

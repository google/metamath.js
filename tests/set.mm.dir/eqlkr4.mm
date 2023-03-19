include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "clvec.mm"
include "wcel.mm"
include "eqid.mm"
include "eqlkr2.mm"
include "syl121anc.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "ldualvs.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem eqlkr4
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
  assume eqlkr4.s: |- S = ( Scalar ` W )
  assume eqlkr4.r: |- R = ( Base ` S )
  assume eqlkr4.f: |- F = ( LFnl ` W )
  assume eqlkr4.k: |- K = ( LKer ` W )
  assume eqlkr4.d: |- D = ( LDual ` W )
  assume eqlkr4.t: |- .x. = ( .s ` D )
  assume eqlkr4.w: |- ( ph -> W e. LVec )
  assume eqlkr4.g: |- ( ph -> G e. F )
  assume eqlkr4.h: |- ( ph -> H e. F )
  assume eqlkr4.e: |- ( ph -> ( K ` G ) = ( K ` H ) )

  disjoint F r
  disjoint G r
  disjoint H r
  disjoint K r
  disjoint R r
  disjoint S r
  disjoint W r
  disjoint ph r
  assert |- ( ph -> E. r e. R H = ( r .x. G ) )

  proof
    wph
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
    cH
    cG
    cW
    cbs
    cfv
    #
    @0
    csn
    cxp
    cS
    cmulr
    cfv
    #
    cof
    co
    #
    wceq
    #
    vr
    cR
    wrex
    #
    wph
    cW
    clvec
    wcel
    #
    cG
    cF
    wcel
    #
    cH
    cF
    wcel
    cG
    cK
    cfv
    cH
    cK
    cfv
    wceq
    @7
    eqlkr4.w
    eqlkr4.g
    eqlkr4.h
    eqlkr4.e
    cS
    @4
    cF
    cG
    cH
    cR
    cK
    @3
    cW
    vr
    eqlkr4.s
    eqlkr4.r
    @4
    eqid
    #
    @3
    eqid
    #
    eqlkr4.f
    eqlkr4.k
    eqlkr2
    syl121anc
    wph
    @2
    @6
    vr
    cR
    wph
    @0
    cR
    wcel
    #
    wa
    #
    @1
    @5
    cH
    @13
    cD
    cS
    c.x
    @4
    cF
    cG
    cR
    @3
    cW
    @0
    clvec
    eqlkr4.f
    @11
    eqlkr4.s
    eqlkr4.r
    @10
    eqlkr4.d
    eqlkr4.t
    wph
    @8
    @12
    eqlkr4.w
    adantr
    wph
    @12
    simpr
    wph
    @9
    @12
    eqlkr4.g
    adantr
    ldualvs
    eqeq2d
    rexbidva
    mpbird
end

include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cmulr.mm"
include "cplusg.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "crio.mm"
include "wa.mm"
include "wreu.mm"
include "clvec.mm"
include "adantr.mm"
include "simpr.mm"
include "csn.mm"
include "lshpsmreu.mm"
include "riotacl.mm"
include "syl.mm"
include "cmpt.mm"
include "weq.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "riotabidv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fmptd.mm"
include "c0g.mm"
include "eqid.mm"
include "lshpkrlem6.mm"
include "ralrimivvva.mm"
include "wb.mm"
include "islfl.mm"
include "mpbir2and.mm"

theorem lshpkrcl
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vl: setvar l
  let vu: setvar u
  let vv: setvar v
  let cL: class L
  assume lshpkr.v: |- V = ( Base ` W )
  assume lshpkr.a: |- .+ = ( +g ` W )
  assume lshpkr.n: |- N = ( LSpan ` W )
  assume lshpkr.p: |- .(+) = ( LSSum ` W )
  assume lshpkr.h: |- H = ( LSHyp ` W )
  assume lshpkr.w: |- ( ph -> W e. LVec )
  assume lshpkr.u: |- ( ph -> U e. H )
  assume lshpkr.z: |- ( ph -> Z e. V )
  assume lshpkr.e: |- ( ph -> ( U .(+) ( N ` { Z } ) ) = V )
  assume lshpkr.d: |- D = ( Scalar ` W )
  assume lshpkr.k: |- K = ( Base ` D )
  assume lshpkr.t: |- .x. = ( .s ` W )
  assume lshpkr.g: |- G = ( x e. V |-> ( iota_ k e. K E. y e. U x = ( y .+ ( k .x. Z ) ) ) )
  assume lshpkr.f: |- F = ( LFnl ` W )

  disjoint k x
  disjoint k y
  disjoint .+ k
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint K k
  disjoint K x
  disjoint U k
  disjoint U x
  disjoint U y
  disjoint D k
  disjoint .x. k
  disjoint .x. x
  disjoint .x. y
  disjoint Z k
  disjoint Z x
  disjoint Z y
  disjoint V x
  disjoint a k
  disjoint a l
  disjoint a x
  disjoint a y
  disjoint .+ a
  disjoint k l
  disjoint l x
  disjoint l y
  disjoint .+ l
  disjoint l u
  disjoint l v
  disjoint G l
  disjoint u v
  disjoint G u
  disjoint G v
  disjoint a u
  disjoint a v
  disjoint K a
  disjoint k u
  disjoint k v
  disjoint K l
  disjoint u x
  disjoint K u
  disjoint v x
  disjoint K v
  disjoint U a
  disjoint U l
  disjoint v y
  disjoint U v
  disjoint u y
  disjoint W l
  disjoint W u
  disjoint W v
  disjoint .x. a
  disjoint .x. l
  disjoint Z a
  disjoint Z l
  disjoint L v
  disjoint a ph
  disjoint l ph
  disjoint ph u
  disjoint ph v
  disjoint V a
  disjoint V u
  disjoint V v
  assert |- ( ph -> G e. F )

  proof
    wph
    cG
    cF
    wcel
    #
    cV
    cK
    cG
    wf
    #
    vl
    cv
    #
    vu
    cv
    #
    c.x
    co
    vv
    cv
    #
    c.pl
    co
    cG
    cfv
    @2
    @3
    cG
    cfv
    cD
    cmulr
    cfv
    #
    co
    @4
    cG
    cfv
    cD
    cplusg
    cfv
    #
    co
    wceq
    #
    vv
    cV
    wral
    vu
    cV
    wral
    vl
    cK
    wral
    #
    wph
    va
    cV
    va
    cv
    #
    vy
    cv
    vk
    cv
    cZ
    c.x
    co
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    #
    vk
    cK
    crio
    #
    cK
    cG
    wph
    @9
    cV
    wcel
    #
    wa
    #
    @12
    vk
    cK
    wreu
    @13
    cK
    wcel
    @15
    vy
    cD
    c.pl
    c.po
    c.x
    cU
    vk
    cH
    cK
    cN
    cV
    cW
    @9
    cZ
    lshpkr.v
    lshpkr.a
    lshpkr.n
    lshpkr.p
    lshpkr.h
    wph
    cW
    clvec
    wcel
    #
    @14
    lshpkr.w
    adantr
    wph
    cU
    cH
    wcel
    @14
    lshpkr.u
    adantr
    wph
    cZ
    cV
    wcel
    @14
    lshpkr.z
    adantr
    wph
    @14
    simpr
    wph
    cU
    cZ
    csn
    cN
    cfv
    c.po
    co
    cV
    wceq
    @14
    lshpkr.e
    adantr
    lshpkr.d
    lshpkr.k
    lshpkr.t
    lshpsmreu
    @12
    vk
    cK
    riotacl
    syl
    cG
    vx
    cV
    vx
    cv
    #
    @10
    wceq
    #
    vy
    cU
    wrex
    #
    vk
    cK
    crio
    #
    cmpt
    va
    cV
    @13
    cmpt
    lshpkr.g
    vx
    va
    cV
    @20
    @13
    vx
    va
    weq
    #
    @19
    @12
    vk
    cK
    @21
    @18
    @11
    vy
    cU
    @17
    @9
    @10
    eqeq1
    rexbidv
    riotabidv
    cbvmptv
    eqtri
    fmptd
    wph
    @7
    vl
    vu
    vv
    cK
    cV
    cV
    wph
    vx
    vy
    vv
    vu
    cD
    c.pl
    c.po
    c.x
    cU
    vk
    cG
    cH
    cK
    cN
    cV
    cW
    cZ
    cD
    c0g
    cfv
    #
    cZ
    vl
    lshpkr.v
    lshpkr.a
    lshpkr.n
    lshpkr.p
    lshpkr.h
    lshpkr.w
    lshpkr.u
    lshpkr.z
    lshpkr.z
    lshpkr.e
    lshpkr.d
    lshpkr.k
    lshpkr.t
    @22
    eqid
    lshpkr.g
    lshpkrlem6
    ralrimivvva
    wph
    @16
    @0
    @1
    @8
    wa
    wb
    lshpkr.w
    vu
    vv
    cD
    c.pl
    @6
    c.x
    @5
    cF
    cG
    cK
    cV
    cW
    clvec
    vl
    lshpkr.v
    lshpkr.a
    lshpkr.d
    lshpkr.t
    lshpkr.k
    @6
    eqid
    @5
    eqid
    lshpkr.f
    islfl
    syl
    mpbir2and
end

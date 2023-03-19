include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "clfn.mm"
include "eqid.mm"
include "clvec.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lshpkrcl.mm"
include "lkrssv.mm"
include "sseld.mm"
include "clss.mm"
include "lshplss.mm"
include "lssel.mm"
include "sylan.mm"
include "ex.mm"
include "wb.mm"
include "wa.mm"
include "c0g.mm"
include "wceq.mm"
include "ellkr.mm"
include "syl2anc.mm"
include "baibd.mm"
include "adantr.mm"
include "simpr.mm"
include "csn.mm"
include "co.mm"
include "lshpkrlem1.mm"
include "bitr4d.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem lshpkr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let c.po: class .(+)
  let c.x: class .x.
  let cU: class U
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let va: setvar a
  let vl: setvar l
  let vu: setvar u
  let vv: setvar v
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
  assume lshpkr.l: |- L = ( LKer ` W )

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
  assert |- ( ph -> ( L ` G ) = U )

  proof
    wph
    vv
    cG
    cL
    cfv
    #
    cU
    wph
    vv
    cv
    #
    cV
    wcel
    #
    @1
    @0
    wcel
    #
    @1
    cU
    wcel
    #
    wph
    @0
    cV
    @1
    wph
    cW
    clfn
    cfv
    #
    cG
    cL
    cV
    cW
    lshpkr.v
    @5
    eqid
    #
    lshpkr.l
    wph
    cW
    clvec
    wcel
    #
    cW
    clmod
    wcel
    lshpkr.w
    cW
    lveclmod
    syl
    #
    wph
    vx
    vy
    cD
    c.pl
    c.po
    c.x
    cU
    vk
    @5
    cG
    cH
    cK
    cN
    cV
    cW
    cZ
    lshpkr.v
    lshpkr.a
    lshpkr.n
    lshpkr.p
    lshpkr.h
    lshpkr.w
    lshpkr.u
    lshpkr.z
    lshpkr.e
    lshpkr.d
    lshpkr.k
    lshpkr.t
    lshpkr.g
    @6
    lshpkrcl
    #
    lkrssv
    sseld
    wph
    @4
    @2
    wph
    cU
    cW
    clss
    cfv
    #
    wcel
    @4
    @2
    wph
    @10
    cU
    cH
    cW
    @10
    eqid
    #
    lshpkr.h
    @8
    lshpkr.u
    lshplss
    @10
    cU
    cV
    cW
    @1
    lshpkr.v
    @11
    lssel
    sylan
    ex
    wph
    @2
    @3
    @4
    wb
    wph
    @2
    wa
    #
    @3
    @1
    cG
    cfv
    cD
    c0g
    cfv
    #
    wceq
    #
    @4
    wph
    @3
    @2
    @14
    wph
    @7
    cG
    @5
    wcel
    @3
    @2
    @14
    wa
    wb
    lshpkr.w
    @9
    cD
    @5
    cG
    cL
    cV
    cW
    @1
    clvec
    @13
    lshpkr.v
    lshpkr.d
    @13
    eqid
    #
    @6
    lshpkr.l
    ellkr
    syl2anc
    baibd
    @12
    vx
    vy
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
    @1
    @13
    cZ
    lshpkr.v
    lshpkr.a
    lshpkr.n
    lshpkr.p
    lshpkr.h
    wph
    @7
    @2
    lshpkr.w
    adantr
    wph
    cU
    cH
    wcel
    @2
    lshpkr.u
    adantr
    wph
    cZ
    cV
    wcel
    @2
    lshpkr.z
    adantr
    wph
    @2
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
    @2
    lshpkr.e
    adantr
    lshpkr.d
    lshpkr.k
    lshpkr.t
    @15
    lshpkr.g
    lshpkrlem1
    bitr4d
    ex
    pm5.21ndd
    eqrdv
end

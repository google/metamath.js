include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cqs.mm"
include "cv.mm"
include "csu.mm"
include "cmul.mm"
include "co.mm"
include "cvtx.mm"
include "cfn.mm"
include "wceq.mm"
include "eqid.mm"
include "fusgrvtxfi.mm"
include "adantr.mm"
include "hashclwwlkn0.mm"
include "syl.mm"
include "cumgr.mm"
include "wi.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "usgrumgr.mm"
include "umgrhashecclwwlk.mm"
include "sylan.mm"
include "imp.mm"
include "sumeq2dv.mm"
include "cc.mm"
include "qerclwwlknfi.mm"
include "prmnn.mm"
include "nncnd.mm"
include "adantl.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem fusgrhashclwwlkn
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vm: setvar m
  let vz: setvar z
  let vk: setvar k
  let cX: class X
  let cB: class B
  let cY: class Y
  let cU: class U
  let vi: setvar i
  assume erclwwlkn.w: |- W = ( N ClWWalksN G )
  assume erclwwlkn.r: |- .~ = { <. t , u >. | ( t e. W /\ u e. W /\ E. n e. ( 0 ... N ) t = ( u cyclShift n ) ) }

  disjoint W t
  disjoint W u
  disjoint t u
  disjoint N n
  disjoint N u
  disjoint N t
  disjoint n u
  disjoint n t
  disjoint W n
  disjoint G n
  disjoint G u
  disjoint N x
  disjoint n x
  disjoint u x
  disjoint t x
  disjoint n y
  disjoint t y
  disjoint u y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint x y
  disjoint N m
  disjoint n z
  disjoint t z
  disjoint u z
  disjoint y z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m z
  disjoint x z
  disjoint N k
  disjoint W k
  disjoint W m
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint W x
  disjoint G x
  disjoint X x
  disjoint B x
  disjoint B y
  disjoint N y
  disjoint W y
  disjoint X y
  disjoint G k
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint Y k
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint G m
  disjoint G y
  disjoint m u
  disjoint U m
  disjoint U n
  disjoint U u
  disjoint U x
  disjoint U y
  disjoint G i
  disjoint i m
  disjoint i x
  disjoint i u
  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> ( # ` W ) = ( ( # ` ( W /. .~ ) ) x. N ) )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cprime
    wcel
    #
    wa
    #
    cW
    chash
    cfv
    #
    cW
    c.sm
    cqs
    #
    vx
    cv
    #
    chash
    cfv
    #
    vx
    csu
    #
    @4
    cN
    vx
    csu
    #
    @4
    chash
    cfv
    cN
    cmul
    co
    #
    @2
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    @3
    @7
    wceq
    @0
    @11
    @1
    cG
    @10
    @10
    eqid
    fusgrvtxfi
    adantr
    #
    vx
    vu
    vt
    c.sm
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    hashclwwlkn0
    syl
    @2
    @4
    @6
    cN
    vx
    @2
    @5
    @4
    wcel
    #
    @6
    cN
    wceq
    #
    @0
    cG
    cumgr
    wcel
    #
    @1
    @13
    @14
    wi
    @0
    cG
    cusgr
    wcel
    @15
    cG
    fusgrusgr
    cG
    usgrumgr
    syl
    vu
    vt
    c.sm
    @5
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    umgrhashecclwwlk
    sylan
    imp
    sumeq2dv
    @2
    @4
    cfn
    wcel
    #
    cN
    cc
    wcel
    #
    @8
    @9
    wceq
    @2
    @11
    @16
    @12
    vu
    vt
    c.sm
    vn
    cG
    cN
    cW
    erclwwlkn.w
    erclwwlkn.r
    qerclwwlknfi
    syl
    @1
    @17
    @0
    @1
    cN
    cN
    prmnn
    nncnd
    adantl
    @4
    cN
    vx
    fsumconst
    syl2anc
    3eqtrd
end

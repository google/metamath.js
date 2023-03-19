include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "clmod.mm"
include "eqid.mm"
include "wcel.mm"
include "lmodacl.mm"
include "syl3anc.mm"
include "ldualvs.mm"
include "lflvsdi2a.mm"
include "ldualvscl.mm"
include "ldualvadd.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"

theorem ldualvsdi2
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ldualvsdi2.f: |- F = ( LFnl ` W )
  assume ldualvsdi2.r: |- R = ( Scalar ` W )
  assume ldualvsdi2.a: |- .+ = ( +g ` R )
  assume ldualvsdi2.k: |- K = ( Base ` R )
  assume ldualvsdi2.d: |- D = ( LDual ` W )
  assume ldualvsdi2.p: |- .+b = ( +g ` D )
  assume ldualvsdi2.s: |- .x. = ( .s ` D )
  assume ldualvsdi2.w: |- ( ph -> W e. LMod )
  assume ldualvsdi2.x: |- ( ph -> X e. K )
  assume ldualvsdi2.y: |- ( ph -> Y e. K )
  assume ldualvsdi2.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( X .+ Y ) .x. G ) = ( ( X .x. G ) .+b ( Y .x. G ) ) )

  proof
    wph
    cX
    cY
    c.pl
    co
    #
    cG
    c.x
    co
    cG
    cW
    cbs
    cfv
    #
    @0
    csn
    cxp
    cR
    cmulr
    cfv
    #
    cof
    #
    co
    cG
    @1
    cX
    csn
    cxp
    @3
    co
    #
    cG
    @1
    cY
    csn
    cxp
    @3
    co
    #
    c.pl
    cof
    #
    co
    #
    cX
    cG
    c.x
    co
    #
    cY
    cG
    c.x
    co
    #
    c.pb
    co
    #
    wph
    cD
    cR
    c.x
    @2
    cF
    cG
    cK
    @1
    cW
    @0
    clmod
    ldualvsdi2.f
    @1
    eqid
    #
    ldualvsdi2.r
    ldualvsdi2.k
    @2
    eqid
    #
    ldualvsdi2.d
    ldualvsdi2.s
    ldualvsdi2.w
    wph
    cW
    clmod
    wcel
    cX
    cK
    wcel
    cY
    cK
    wcel
    @0
    cK
    wcel
    ldualvsdi2.w
    ldualvsdi2.x
    ldualvsdi2.y
    c.pl
    cR
    cK
    cW
    cX
    cY
    ldualvsdi2.r
    ldualvsdi2.k
    ldualvsdi2.a
    lmodacl
    syl3anc
    ldualvsdi2.g
    ldualvs
    wph
    c.pl
    cR
    @2
    cF
    cG
    cK
    @1
    cW
    cX
    cY
    @11
    ldualvsdi2.r
    ldualvsdi2.k
    ldualvsdi2.a
    @12
    ldualvsdi2.f
    ldualvsdi2.w
    ldualvsdi2.x
    ldualvsdi2.y
    ldualvsdi2.g
    lflvsdi2a
    wph
    @10
    @8
    @9
    @6
    co
    @7
    wph
    cD
    c.pl
    c.pb
    cR
    cF
    @8
    @9
    cW
    clmod
    ldualvsdi2.f
    ldualvsdi2.r
    ldualvsdi2.a
    ldualvsdi2.d
    ldualvsdi2.p
    ldualvsdi2.w
    wph
    cD
    cR
    c.x
    cF
    cG
    cK
    cW
    cX
    ldualvsdi2.f
    ldualvsdi2.r
    ldualvsdi2.k
    ldualvsdi2.d
    ldualvsdi2.s
    ldualvsdi2.w
    ldualvsdi2.x
    ldualvsdi2.g
    ldualvscl
    wph
    cD
    cR
    c.x
    cF
    cG
    cK
    cW
    cY
    ldualvsdi2.f
    ldualvsdi2.r
    ldualvsdi2.k
    ldualvsdi2.d
    ldualvsdi2.s
    ldualvsdi2.w
    ldualvsdi2.y
    ldualvsdi2.g
    ldualvscl
    ldualvadd
    wph
    @8
    @4
    @9
    @5
    @6
    wph
    cD
    cR
    c.x
    @2
    cF
    cG
    cK
    @1
    cW
    cX
    clmod
    ldualvsdi2.f
    @11
    ldualvsdi2.r
    ldualvsdi2.k
    @12
    ldualvsdi2.d
    ldualvsdi2.s
    ldualvsdi2.w
    ldualvsdi2.x
    ldualvsdi2.g
    ldualvs
    wph
    cD
    cR
    c.x
    @2
    cF
    cG
    cK
    @1
    cW
    cY
    clmod
    ldualvsdi2.f
    @11
    ldualvsdi2.r
    ldualvsdi2.k
    @12
    ldualvsdi2.d
    ldualvsdi2.s
    ldualvsdi2.w
    ldualvsdi2.y
    ldualvsdi2.g
    ldualvs
    oveq12d
    eqtr2d
    3eqtrd
end

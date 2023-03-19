include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "cbs.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualvs.mm"
include "oveq12d.mm"
include "ldualvscl.mm"
include "ldualvadd.mm"
include "ldualvaddcl.mm"
include "oveq1d.mm"
include "lflvsdi1.mm"
include "3eqtrd.mm"
include "3eqtr4rd.mm"

theorem ldualvsdi1
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  assume ldualvsdi1.f: |- F = ( LFnl ` W )
  assume ldualvsdi1.r: |- R = ( Scalar ` W )
  assume ldualvsdi1.k: |- K = ( Base ` R )
  assume ldualvsdi1.d: |- D = ( LDual ` W )
  assume ldualvsdi1.p: |- .+ = ( +g ` D )
  assume ldualvsdi1.s: |- .x. = ( .s ` D )
  assume ldualvsdi1.w: |- ( ph -> W e. LMod )
  assume ldualvsdi1.x: |- ( ph -> X e. K )
  assume ldualvsdi1.g: |- ( ph -> G e. F )
  assume ldualvsdi1.h: |- ( ph -> H e. F )


  assert |- ( ph -> ( X .x. ( G .+ H ) ) = ( ( X .x. G ) .+ ( X .x. H ) ) )

  proof
    wph
    cX
    cG
    c.x
    co
    #
    cX
    cH
    c.x
    co
    #
    cR
    cplusg
    cfv
    #
    cof
    #
    co
    cG
    cW
    cbs
    cfv
    #
    cX
    csn
    cxp
    #
    cR
    cmulr
    cfv
    #
    cof
    #
    co
    #
    cH
    @5
    @7
    co
    #
    @3
    co
    #
    @0
    @1
    c.pl
    co
    cX
    cG
    cH
    c.pl
    co
    #
    c.x
    co
    #
    wph
    @0
    @8
    @1
    @9
    @3
    wph
    cD
    cR
    c.x
    @6
    cF
    cG
    cK
    @4
    cW
    cX
    clmod
    ldualvsdi1.f
    @4
    eqid
    #
    ldualvsdi1.r
    ldualvsdi1.k
    @6
    eqid
    #
    ldualvsdi1.d
    ldualvsdi1.s
    ldualvsdi1.w
    ldualvsdi1.x
    ldualvsdi1.g
    ldualvs
    wph
    cD
    cR
    c.x
    @6
    cF
    cH
    cK
    @4
    cW
    cX
    clmod
    ldualvsdi1.f
    @13
    ldualvsdi1.r
    ldualvsdi1.k
    @14
    ldualvsdi1.d
    ldualvsdi1.s
    ldualvsdi1.w
    ldualvsdi1.x
    ldualvsdi1.h
    ldualvs
    oveq12d
    wph
    cD
    @2
    c.pl
    cR
    cF
    @0
    @1
    cW
    clmod
    ldualvsdi1.f
    ldualvsdi1.r
    @2
    eqid
    #
    ldualvsdi1.d
    ldualvsdi1.p
    ldualvsdi1.w
    wph
    cD
    cR
    c.x
    cF
    cG
    cK
    cW
    cX
    ldualvsdi1.f
    ldualvsdi1.r
    ldualvsdi1.k
    ldualvsdi1.d
    ldualvsdi1.s
    ldualvsdi1.w
    ldualvsdi1.x
    ldualvsdi1.g
    ldualvscl
    wph
    cD
    cR
    c.x
    cF
    cH
    cK
    cW
    cX
    ldualvsdi1.f
    ldualvsdi1.r
    ldualvsdi1.k
    ldualvsdi1.d
    ldualvsdi1.s
    ldualvsdi1.w
    ldualvsdi1.x
    ldualvsdi1.h
    ldualvscl
    ldualvadd
    wph
    @12
    @11
    @5
    @7
    co
    cG
    cH
    @3
    co
    #
    @5
    @7
    co
    @10
    wph
    cD
    cR
    c.x
    @6
    cF
    @11
    cK
    @4
    cW
    cX
    clmod
    ldualvsdi1.f
    @13
    ldualvsdi1.r
    ldualvsdi1.k
    @14
    ldualvsdi1.d
    ldualvsdi1.s
    ldualvsdi1.w
    ldualvsdi1.x
    wph
    cD
    c.pl
    cF
    cG
    cH
    cW
    ldualvsdi1.f
    ldualvsdi1.d
    ldualvsdi1.p
    ldualvsdi1.w
    ldualvsdi1.g
    ldualvsdi1.h
    ldualvaddcl
    ldualvs
    wph
    @11
    @16
    @5
    @7
    wph
    cD
    @2
    c.pl
    cR
    cF
    cG
    cH
    cW
    clmod
    ldualvsdi1.f
    ldualvsdi1.r
    @15
    ldualvsdi1.d
    ldualvsdi1.p
    ldualvsdi1.w
    ldualvsdi1.g
    ldualvsdi1.h
    ldualvadd
    oveq1d
    wph
    @2
    cR
    @6
    cF
    cG
    cH
    cK
    @4
    cW
    cX
    @13
    ldualvsdi1.r
    ldualvsdi1.k
    @15
    @14
    ldualvsdi1.f
    ldualvsdi1.w
    ldualvsdi1.x
    ldualvsdi1.g
    ldualvsdi1.h
    lflvsdi1
    3eqtrd
    3eqtr4rd
end

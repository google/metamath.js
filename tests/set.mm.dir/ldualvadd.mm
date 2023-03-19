include "co.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "ldualfvadd.mm"
include "oveqd.mm"
include "ofmresval.mm"
include "eqtrd.mm"

theorem ldualvadd
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  assume ldualvadd.f: |- F = ( LFnl ` W )
  assume ldualvadd.r: |- R = ( Scalar ` W )
  assume ldualvadd.a: |- .+ = ( +g ` R )
  assume ldualvadd.d: |- D = ( LDual ` W )
  assume ldualvadd.p: |- .+b = ( +g ` D )
  assume ldualvadd.w: |- ( ph -> W e. X )
  assume ldualvadd.g: |- ( ph -> G e. F )
  assume ldualvadd.h: |- ( ph -> H e. F )


  assert |- ( ph -> ( G .+b H ) = ( G oF .+ H ) )

  proof
    wph
    cG
    cH
    c.pb
    co
    cG
    cH
    c.pl
    cof
    #
    cF
    cF
    cxp
    cres
    #
    co
    cG
    cH
    @0
    co
    wph
    c.pb
    @1
    cG
    cH
    wph
    cD
    c.pl
    @1
    c.pb
    cR
    cF
    cW
    cX
    ldualvadd.f
    ldualvadd.r
    ldualvadd.a
    ldualvadd.d
    ldualvadd.p
    ldualvadd.w
    @1
    eqid
    ldualfvadd
    oveqd
    wph
    cF
    cF
    c.pl
    cG
    cH
    ldualvadd.g
    ldualvadd.h
    ofmresval
    eqtrd
end

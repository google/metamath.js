include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "cminusg.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "lduallmod.mm"
include "eqid.mm"
include "ldualelvbase.mm"
include "lmodvsubval2.mm"
include "syl3anc.mm"
include "coppr.mm"
include "ldualsca.mm"
include "fveq2d.mm"
include "opprneg.mm"
include "syl6reqr.mm"
include "oppr1.mm"
include "fveq12d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem ldualvsub
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cN: class N
  let cW: class W
  assume ldualvsub.r: |- R = ( Scalar ` W )
  assume ldualvsub.n: |- N = ( invg ` R )
  assume ldualvsub.u: |- .1. = ( 1r ` R )
  assume ldualvsub.f: |- F = ( LFnl ` W )
  assume ldualvsub.d: |- D = ( LDual ` W )
  assume ldualvsub.p: |- .+ = ( +g ` D )
  assume ldualvsub.t: |- .x. = ( .s ` D )
  assume ldualvsub.m: |- .- = ( -g ` D )
  assume ldualvsub.w: |- ( ph -> W e. LMod )
  assume ldualvsub.g: |- ( ph -> G e. F )
  assume ldualvsub.h: |- ( ph -> H e. F )


  assert |- ( ph -> ( G .- H ) = ( G .+ ( ( N ` .1. ) .x. H ) ) )

  proof
    wph
    cG
    cH
    c.mi
    co
    #
    cG
    cD
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    cminusg
    cfv
    #
    cfv
    #
    cH
    c.x
    co
    #
    c.pl
    co
    #
    cG
    c.1
    cN
    cfv
    #
    cH
    c.x
    co
    #
    c.pl
    co
    wph
    cD
    clmod
    wcel
    cG
    cD
    cbs
    cfv
    #
    wcel
    cH
    @9
    wcel
    @0
    @6
    wceq
    wph
    cD
    cW
    ldualvsub.d
    ldualvsub.w
    lduallmod
    wph
    cD
    cF
    cG
    @9
    cW
    clmod
    ldualvsub.f
    ldualvsub.d
    @9
    eqid
    #
    ldualvsub.w
    ldualvsub.g
    ldualelvbase
    wph
    cD
    cF
    cH
    @9
    cW
    clmod
    ldualvsub.f
    ldualvsub.d
    @10
    ldualvsub.w
    ldualvsub.h
    ldualelvbase
    cG
    cH
    c.pl
    c.x
    @2
    @1
    c.mi
    @3
    @9
    cD
    @10
    ldualvsub.p
    ldualvsub.m
    @1
    eqid
    #
    ldualvsub.t
    @3
    eqid
    @2
    eqid
    lmodvsubval2
    syl3anc
    wph
    @8
    @5
    cG
    c.pl
    wph
    @7
    @4
    cH
    c.x
    wph
    c.1
    @2
    cN
    @3
    wph
    @3
    cR
    coppr
    cfv
    #
    cminusg
    cfv
    cN
    wph
    @1
    @12
    cminusg
    wph
    cD
    @1
    cR
    @12
    cW
    clmod
    ldualvsub.r
    @12
    eqid
    #
    ldualvsub.d
    @11
    ldualvsub.w
    ldualsca
    #
    fveq2d
    cR
    cN
    @12
    @13
    ldualvsub.n
    opprneg
    syl6reqr
    wph
    @2
    @12
    cur
    cfv
    c.1
    wph
    @1
    @12
    cur
    @14
    fveq2d
    cR
    c.1
    @12
    @13
    ldualvsub.u
    oppr1
    syl6reqr
    fveq12d
    oveq1d
    oveq2d
    eqtr4d
end

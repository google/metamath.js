include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cplusg.mm"
include "cof.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualvadd.mm"
include "lfladdcl.mm"
include "eqeltrd.mm"

theorem ldualvaddcl
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  assume ldualvaddcl.f: |- F = ( LFnl ` W )
  assume ldualvaddcl.d: |- D = ( LDual ` W )
  assume ldualvaddcl.p: |- .+ = ( +g ` D )
  assume ldualvaddcl.w: |- ( ph -> W e. LMod )
  assume ldualvaddcl.g: |- ( ph -> G e. F )
  assume ldualvaddcl.h: |- ( ph -> H e. F )


  assert |- ( ph -> ( G .+ H ) e. F )

  proof
    wph
    cG
    cH
    c.pl
    co
    cG
    cH
    cW
    csca
    cfv
    #
    cplusg
    cfv
    #
    cof
    co
    cF
    wph
    cD
    @1
    c.pl
    @0
    cF
    cG
    cH
    cW
    clmod
    ldualvaddcl.f
    @0
    eqid
    #
    @1
    eqid
    #
    ldualvaddcl.d
    ldualvaddcl.p
    ldualvaddcl.w
    ldualvaddcl.g
    ldualvaddcl.h
    ldualvadd
    wph
    @1
    @0
    cF
    cG
    cH
    cW
    @2
    @3
    ldualvaddcl.f
    ldualvaddcl.w
    ldualvaddcl.g
    ldualvaddcl.h
    lfladdcl
    eqeltrd
end

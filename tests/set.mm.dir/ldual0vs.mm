include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "co.mm"
include "eqid.mm"
include "ldual0.mm"
include "oveq1d.mm"
include "clmod.mm"
include "wcel.mm"
include "cbs.mm"
include "wceq.mm"
include "lduallmod.mm"
include "ldualelvbase.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem ldual0vs
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cO: class O
  let cW: class W
  let c.0: class .0.
  assume ldual0vs.f: |- F = ( LFnl ` W )
  assume ldual0vs.r: |- R = ( Scalar ` W )
  assume ldual0vs.z: |- .0. = ( 0g ` R )
  assume ldual0vs.d: |- D = ( LDual ` W )
  assume ldual0vs.t: |- .x. = ( .s ` D )
  assume ldual0vs.o: |- O = ( 0g ` D )
  assume ldual0vs.w: |- ( ph -> W e. LMod )
  assume ldual0vs.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( .0. .x. G ) = O )

  proof
    wph
    cD
    csca
    cfv
    #
    c0g
    cfv
    #
    cG
    c.x
    co
    #
    c.0
    cG
    c.x
    co
    cO
    wph
    @1
    c.0
    cG
    c.x
    wph
    cD
    cR
    @0
    @1
    cW
    c.0
    ldual0vs.r
    ldual0vs.z
    ldual0vs.d
    @0
    eqid
    #
    @1
    eqid
    #
    ldual0vs.w
    ldual0
    oveq1d
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
    @2
    cO
    wceq
    wph
    cD
    cW
    ldual0vs.d
    ldual0vs.w
    lduallmod
    wph
    cD
    cF
    cG
    @5
    cW
    clmod
    ldual0vs.f
    ldual0vs.d
    @5
    eqid
    #
    ldual0vs.w
    ldual0vs.g
    ldualelvbase
    c.x
    @0
    @1
    @5
    cD
    cG
    cO
    @6
    @3
    ldual0vs.t
    @4
    ldual0vs.o
    lmod0vs
    syl2anc
    eqtr3d
end

include "co.mm"
include "cfv.mm"
include "cminusg.mm"
include "cneg.mm"
include "eqid.mm"
include "cclm.mm"
include "wcel.mm"
include "clmod.mm"
include "clmlmod.mm"
include "syl.mm"
include "lmodvsneg.mm"
include "wceq.mm"
include "clmneg.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "eqtr4d.mm"

theorem clmvsneg
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cN: class N
  let cW: class W
  let cX: class X
  assume clmvsneg.b: |- B = ( Base ` W )
  assume clmvsneg.f: |- F = ( Scalar ` W )
  assume clmvsneg.s: |- .x. = ( .s ` W )
  assume clmvsneg.n: |- N = ( invg ` W )
  assume clmvsneg.k: |- K = ( Base ` F )
  assume clmvsneg.w: |- ( ph -> W e. CMod )
  assume clmvsneg.x: |- ( ph -> X e. B )
  assume clmvsneg.r: |- ( ph -> R e. K )


  assert |- ( ph -> ( N ` ( R .x. X ) ) = ( -u R .x. X ) )

  proof
    wph
    cR
    cX
    c.x
    co
    cN
    cfv
    cR
    cF
    cminusg
    cfv
    #
    cfv
    #
    cX
    c.x
    co
    cR
    cneg
    #
    cX
    c.x
    co
    wph
    cB
    cR
    c.x
    cF
    cK
    @0
    cN
    cW
    cX
    clmvsneg.b
    clmvsneg.f
    clmvsneg.s
    clmvsneg.n
    clmvsneg.k
    @0
    eqid
    wph
    cW
    cclm
    wcel
    #
    cW
    clmod
    wcel
    clmvsneg.w
    cW
    clmlmod
    syl
    clmvsneg.x
    clmvsneg.r
    lmodvsneg
    wph
    @2
    @1
    cX
    c.x
    wph
    @3
    cR
    cK
    wcel
    @2
    @1
    wceq
    clmvsneg.w
    clmvsneg.r
    cR
    cF
    cK
    cW
    clmvsneg.f
    clmvsneg.k
    clmneg
    syl2anc
    oveq1d
    eqtr4d
end

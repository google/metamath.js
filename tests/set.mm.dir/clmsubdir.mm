include "cmin.mm"
include "co.mm"
include "csg.mm"
include "cfv.mm"
include "cclm.mm"
include "wcel.mm"
include "wceq.mm"
include "clmsub.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqid.mm"
include "clmod.mm"
include "clmlmod.mm"
include "syl.mm"
include "lmodsubdir.mm"
include "eqtrd.mm"

theorem clmsubdir
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  assume clmsubdir.v: |- V = ( Base ` W )
  assume clmsubdir.t: |- .x. = ( .s ` W )
  assume clmsubdir.f: |- F = ( Scalar ` W )
  assume clmsubdir.k: |- K = ( Base ` F )
  assume clmsubdir.m: |- .- = ( -g ` W )
  assume clmsubdir.w: |- ( ph -> W e. CMod )
  assume clmsubdir.a: |- ( ph -> A e. K )
  assume clmsubdir.b: |- ( ph -> B e. K )
  assume clmsubdir.x: |- ( ph -> X e. V )


  assert |- ( ph -> ( ( A - B ) .x. X ) = ( ( A .x. X ) .- ( B .x. X ) ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cX
    c.x
    co
    cA
    cB
    cF
    csg
    cfv
    #
    co
    #
    cX
    c.x
    co
    cA
    cX
    c.x
    co
    cB
    cX
    c.x
    co
    c.mi
    co
    wph
    @0
    @2
    cX
    c.x
    wph
    cW
    cclm
    wcel
    #
    cA
    cK
    wcel
    cB
    cK
    wcel
    @0
    @2
    wceq
    clmsubdir.w
    clmsubdir.a
    clmsubdir.b
    cA
    cB
    cF
    cK
    cW
    clmsubdir.f
    clmsubdir.k
    clmsub
    syl3anc
    oveq1d
    wph
    cA
    cB
    @1
    c.x
    cF
    cK
    c.mi
    cV
    cW
    cX
    clmsubdir.v
    clmsubdir.t
    clmsubdir.f
    clmsubdir.k
    clmsubdir.m
    @1
    eqid
    wph
    @3
    cW
    clmod
    wcel
    clmsubdir.w
    cW
    clmlmod
    syl
    clmsubdir.a
    clmsubdir.b
    clmsubdir.x
    lmodsubdir
    eqtrd
end

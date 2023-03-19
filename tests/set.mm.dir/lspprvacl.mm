include "clmod.mm"
include "wcel.mm"
include "cpr.mm"
include "cfv.mm"
include "clss.mm"
include "co.mm"
include "eqid.mm"
include "lspprcl.mm"
include "lspprid1.mm"
include "lspprid2.mm"
include "lssvacl.mm"
include "syl22anc.mm"

theorem lspprvacl
  let wph: wff ph
  let c.pl: class .+
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lspprvacl.v: |- V = ( Base ` W )
  assume lspprvacl.p: |- .+ = ( +g ` W )
  assume lspprvacl.n: |- N = ( LSpan ` W )
  assume lspprvacl.w: |- ( ph -> W e. LMod )
  assume lspprvacl.x: |- ( ph -> X e. V )
  assume lspprvacl.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( X .+ Y ) e. ( N ` { X , Y } ) )

  proof
    wph
    cW
    clmod
    wcel
    cX
    cY
    cpr
    cN
    cfv
    #
    cW
    clss
    cfv
    #
    wcel
    cX
    @0
    wcel
    cY
    @0
    wcel
    cX
    cY
    c.pl
    co
    @0
    wcel
    lspprvacl.w
    wph
    @1
    cN
    cV
    cW
    cX
    cY
    lspprvacl.v
    @1
    eqid
    #
    lspprvacl.n
    lspprvacl.w
    lspprvacl.x
    lspprvacl.y
    lspprcl
    wph
    cN
    cV
    cW
    cX
    cY
    lspprvacl.v
    lspprvacl.n
    lspprvacl.w
    lspprvacl.x
    lspprvacl.y
    lspprid1
    wph
    cN
    cV
    cW
    cX
    cY
    lspprvacl.v
    lspprvacl.n
    lspprvacl.w
    lspprvacl.x
    lspprvacl.y
    lspprid2
    c.pl
    @1
    @0
    cW
    cX
    cY
    lspprvacl.p
    @2
    lssvacl
    syl22anc
end

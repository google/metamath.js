include "ctdrg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "ctgp.mm"
include "crest.mm"
include "ccn.mm"
include "eqid.mm"
include "tdrgunit.mm"
include "mgptopn.mm"
include "resstopn.mm"
include "invrfval.mm"
include "tgpinv.mm"
include "syl.mm"

theorem invrcn2
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  assume mulrcn.j: |- J = ( TopOpen ` R )
  assume invrcn.i: |- I = ( invr ` R )
  assume invrcn.u: |- U = ( Unit ` R )


  assert |- ( R e. TopDRing -> I e. ( ( J |`t U ) Cn ( J |`t U ) ) )

  proof
    cR
    ctdrg
    wcel
    cR
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    ctgp
    wcel
    cI
    cJ
    cU
    crest
    co
    #
    @2
    ccn
    co
    wcel
    cR
    cU
    @0
    @0
    eqid
    #
    invrcn.u
    tdrgunit
    @1
    cI
    @2
    cU
    @1
    cJ
    @0
    @1
    eqid
    #
    cR
    cJ
    @0
    @3
    mulrcn.j
    mgptopn
    resstopn
    cR
    cU
    @1
    cI
    invrcn.u
    @4
    invrcn.i
    invrfval
    tgpinv
    syl
end

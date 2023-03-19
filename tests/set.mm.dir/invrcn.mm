include "ctdrg.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "ctps.mm"
include "ctop.mm"
include "wss.mm"
include "tdrgtps.mm"
include "tpstop.mm"
include "cnrest2r.mm"
include "3syl.mm"
include "invrcn2.mm"
include "sseldd.mm"

theorem invrcn
  let cR: class R
  let cU: class U
  let cI: class I
  let cJ: class J
  assume mulrcn.j: |- J = ( TopOpen ` R )
  assume invrcn.i: |- I = ( invr ` R )
  assume invrcn.u: |- U = ( Unit ` R )


  assert |- ( R e. TopDRing -> I e. ( ( J |`t U ) Cn J ) )

  proof
    cR
    ctdrg
    wcel
    #
    cJ
    cU
    crest
    co
    #
    @1
    ccn
    co
    #
    @1
    cJ
    ccn
    co
    #
    cI
    @0
    cR
    ctps
    wcel
    cJ
    ctop
    wcel
    @2
    @3
    wss
    cR
    tdrgtps
    cJ
    cR
    mulrcn.j
    tpstop
    cU
    @1
    cJ
    cnrest2r
    3syl
    cR
    cU
    cI
    cJ
    mulrcn.j
    invrcn.i
    invrcn.u
    invrcn2
    sseldd
end

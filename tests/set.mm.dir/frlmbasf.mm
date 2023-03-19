include "wcel.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "frlmbasmap.mm"
include "wb.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "mpan.mm"
include "adantr.mm"
include "mpbid.mm"

theorem frlmbasf
  let cB: class B
  let cR: class R
  let cF: class F
  let cI: class I
  let cN: class N
  let cW: class W
  let cX: class X
  let vr: setvar r
  let vi: setvar i
  assume frlmval.f: |- F = ( R freeLMod I )
  assume frlmbasmap.n: |- N = ( Base ` R )
  assume frlmbasmap.b: |- B = ( Base ` F )


  assert |- ( ( I e. W /\ X e. B ) -> X : I --> N )

  proof
    cI
    cW
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    cX
    cN
    cI
    cmap
    co
    wcel
    #
    cI
    cN
    cX
    wf
    #
    cB
    cR
    cF
    cI
    cN
    cW
    cX
    frlmval.f
    frlmbasmap.n
    frlmbasmap.b
    frlmbasmap
    @0
    @2
    @3
    wb
    #
    @1
    cN
    cvv
    wcel
    @0
    @4
    cN
    cR
    cbs
    cfv
    cvv
    frlmbasmap.n
    cR
    cbs
    fvex
    eqeltri
    cN
    cI
    cX
    cvv
    cW
    elmapg
    mpan
    adantr
    mpbid
end

include "wcel.mm"
include "crrx.mm"
include "cfv.mm"
include "crefld.mm"
include "cfrlm.mm"
include "co.mm"
include "ctch.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cv.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "df-rrx.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem rrxval
  let cH: class H
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let cB: class B
  let vi: setvar i
  assume rrxval.r: |- H = ( RR^ ` I )


  assert |- ( I e. V -> H = ( toCHil ` ( RRfld freeLMod I ) ) )

  proof
    cI
    cV
    wcel
    #
    cH
    cI
    crrx
    cfv
    #
    crefld
    cI
    cfrlm
    co
    #
    ctch
    cfv
    #
    rrxval.r
    @0
    cI
    cvv
    wcel
    @1
    @3
    wceq
    cI
    cV
    elex
    vi
    cI
    crefld
    vi
    cv
    #
    cfrlm
    co
    #
    ctch
    cfv
    @3
    cvv
    crrx
    @4
    cI
    wceq
    @5
    @2
    ctch
    @4
    cI
    crefld
    cfrlm
    oveq2
    fveq2d
    vi
    df-rrx
    @2
    ctch
    fvex
    fvmpt
    syl
    syl5eq
end

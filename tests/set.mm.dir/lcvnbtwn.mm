include "wpss.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "wbr.mm"
include "lcvbr.mm"
include "mpbid.mm"
include "simprd.mm"
include "wcel.mm"
include "wceq.mm"
include "psseq2.mm"
include "psseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "sylan.mm"
include "mtand.mm"

theorem lcvnbtwn
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cW: class W
  let cX: class X
  let vu: setvar u
  assume lcvnbtwn.s: |- S = ( LSubSp ` W )
  assume lcvnbtwn.c: |- C = ( <oL ` W )
  assume lcvnbtwn.w: |- ( ph -> W e. X )
  assume lcvnbtwn.r: |- ( ph -> R e. S )
  assume lcvnbtwn.t: |- ( ph -> T e. S )
  assume lcvnbtwn.u: |- ( ph -> U e. S )
  assume lcvnbtwn.d: |- ( ph -> R C T )


  assert |- ( ph -> -. ( R C. U /\ U C. T ) )

  proof
    wph
    cR
    cU
    wpss
    #
    cU
    cT
    wpss
    #
    wa
    #
    cR
    vu
    cv
    #
    wpss
    #
    @3
    cT
    wpss
    #
    wa
    #
    vu
    cS
    wrex
    #
    wph
    cR
    cT
    wpss
    #
    @7
    wn
    #
    wph
    cR
    cT
    cC
    wbr
    @8
    @9
    wa
    lcvnbtwn.d
    wph
    cC
    cS
    cR
    cT
    cW
    cX
    vu
    lcvnbtwn.s
    lcvnbtwn.c
    lcvnbtwn.w
    lcvnbtwn.r
    lcvnbtwn.t
    lcvbr
    mpbid
    simprd
    wph
    cU
    cS
    wcel
    @2
    @7
    lcvnbtwn.u
    @6
    @2
    vu
    cU
    cS
    @3
    cU
    wceq
    @4
    @0
    @5
    @1
    @3
    cU
    cR
    psseq2
    @3
    cU
    cT
    psseq1
    anbi12d
    rspcev
    sylan
    mtand
end

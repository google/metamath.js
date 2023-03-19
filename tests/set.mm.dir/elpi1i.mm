include "cphtpc.mm"
include "cfv.mm"
include "cec.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "eceq1.mm"
include "eqcomd.mm"
include "biantrud.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "bitr3d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "elpi1.mm"
include "mpbird.mm"

theorem elpi1i
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let c.pl: class .+
  let vf: setvar f
  let cM: class M
  let cN: class N
  assume elpi1.g: |- G = ( J pi1 Y )
  assume elpi1.b: |- B = ( Base ` G )
  assume elpi1.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume elpi1.2: |- ( ph -> Y e. X )
  assume elpi1i.3: |- ( ph -> F e. ( II Cn J ) )
  assume elpi1i.4: |- ( ph -> ( F ` 0 ) = Y )
  assume elpi1i.5: |- ( ph -> ( F ` 1 ) = Y )


  assert |- ( ph -> [ F ] ( ~=ph ` J ) e. B )

  proof
    wph
    cF
    cJ
    cphtpc
    cfv
    #
    cec
    #
    cB
    wcel
    cc0
    vf
    cv
    #
    cfv
    #
    cY
    wceq
    #
    c1
    @2
    cfv
    #
    cY
    wceq
    #
    wa
    #
    @1
    @2
    @0
    cec
    #
    wceq
    #
    wa
    #
    vf
    cii
    cJ
    ccn
    co
    #
    wrex
    #
    wph
    cF
    @11
    wcel
    cc0
    cF
    cfv
    #
    cY
    wceq
    #
    c1
    cF
    cfv
    #
    cY
    wceq
    #
    @12
    elpi1i.3
    elpi1i.4
    elpi1i.5
    @10
    @14
    @16
    wa
    #
    vf
    cF
    @11
    @2
    cF
    wceq
    #
    @7
    @10
    @17
    @18
    @9
    @7
    @18
    @8
    @1
    @2
    cF
    @0
    eceq1
    eqcomd
    biantrud
    @18
    @4
    @14
    @6
    @16
    @18
    @3
    @13
    cY
    cc0
    @2
    cF
    fveq1
    eqeq1d
    @18
    @5
    @15
    cY
    c1
    @2
    cF
    fveq1
    eqeq1d
    anbi12d
    bitr3d
    rspcev
    syl12anc
    wph
    cB
    vf
    @1
    cG
    cJ
    cX
    cY
    elpi1.g
    elpi1.b
    elpi1.1
    elpi1.2
    elpi1
    mpbird
end

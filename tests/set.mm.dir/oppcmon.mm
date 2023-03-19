include "co.mm"
include "ctpos.mm"
include "cepi.mm"
include "cfv.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "coppc.mm"
include "cmon.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "tposeqd.mm"
include "df-epi.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "tposex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "ovtpos.mm"
include "syl6req.mm"

theorem oppcmon
  let wph: wff ph
  let cC: class C
  let cE: class E
  let cM: class M
  let cO: class O
  let cX: class X
  let cY: class Y
  let vc: setvar c
  assume oppcmon.o: |- O = ( oppCat ` C )
  assume oppcmon.c: |- ( ph -> C e. Cat )
  assume oppcmon.m: |- M = ( Mono ` O )
  assume oppcmon.e: |- E = ( Epi ` C )


  assert |- ( ph -> ( X M Y ) = ( Y E X ) )

  proof
    wph
    cY
    cX
    cE
    co
    cY
    cX
    cM
    ctpos
    #
    co
    cX
    cY
    cM
    co
    wph
    cE
    @0
    cY
    cX
    wph
    cE
    cC
    cepi
    cfv
    #
    @0
    oppcmon.e
    wph
    cC
    ccat
    wcel
    @1
    @0
    wceq
    oppcmon.c
    vc
    cC
    vc
    cv
    #
    coppc
    cfv
    #
    cmon
    cfv
    #
    ctpos
    @0
    ccat
    cepi
    @2
    cC
    wceq
    #
    @4
    cM
    @5
    @4
    cO
    cmon
    cfv
    #
    cM
    @5
    @3
    cO
    cmon
    @5
    @3
    cC
    coppc
    cfv
    cO
    @2
    cC
    coppc
    fveq2
    oppcmon.o
    syl6eqr
    fveq2d
    oppcmon.m
    syl6eqr
    tposeqd
    vc
    df-epi
    cM
    cM
    @6
    cvv
    oppcmon.m
    cO
    cmon
    fvex
    eqeltri
    tposex
    fvmpt
    syl
    syl5eq
    oveqd
    cY
    cX
    cM
    ovtpos
    syl6req
end

include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "lmicl.mm"
include "lmireu.mm"
include "eqidd.mm"
include "reu2eqd.mm"

theorem lmieq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let vb: setvar b
  let vm: setvar m
  let va: setvar a
  let vg: setvar g
  let vd: setvar d
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume lmif.m: |- M = ( ( lInvG ` G ) ` D )
  assume lmif.l: |- L = ( LineG ` G )
  assume lmif.d: |- ( ph -> D e. ran L )
  assume lmicl.1: |- ( ph -> A e. P )
  assume lmieq.c: |- ( ph -> B e. P )
  assume lmieq.d: |- ( ph -> ( M ` A ) = ( M ` B ) )


  assert |- ( ph -> A = B )

  proof
    wph
    vb
    cv
    #
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    wceq
    cA
    cM
    cfv
    #
    @2
    wceq
    @2
    @2
    wceq
    vb
    cP
    cA
    cB
    @0
    cA
    wceq
    @1
    @3
    @2
    @0
    cA
    cM
    fveq2
    eqeq1d
    @0
    cB
    wceq
    @1
    @2
    @2
    @0
    cB
    cM
    fveq2
    eqeq1d
    wph
    @2
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    vb
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    wph
    cB
    cD
    cP
    cG
    cI
    cL
    cM
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    lmieq.c
    lmicl
    lmireu
    lmicl.1
    lmieq.c
    lmieq.d
    wph
    @2
    eqidd
    reu2eqd
end

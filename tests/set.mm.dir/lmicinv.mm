include "cfv.mm"
include "wceq.mm"
include "wcel.mm"
include "lmiinv.mm"
include "mpbird.mm"

theorem lmicinv
  let wph: wff ph
  let cA: class A
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
  assume lmicinv.1: |- ( ph -> A e. D )


  assert |- ( ph -> ( M ` A ) = A )

  proof
    wph
    cA
    cM
    cfv
    cA
    wceq
    cA
    cD
    wcel
    lmicinv.1
    wph
    cA
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
    lmicl.1
    lmiinv
    mpbird
end

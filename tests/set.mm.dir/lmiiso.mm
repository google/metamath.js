include "cfv.mm"
include "cmid.mm"
include "co.mm"
include "cmir.mm"
include "eqid.mm"
include "lmiisolem.mm"

theorem lmiiso
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
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
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
  assume lmiiso.1: |- ( ph -> A e. P )
  assume lmiiso.2: |- ( ph -> B e. P )


  assert |- ( ph -> ( ( M ` A ) .- ( M ` B ) ) = ( A .- B ) )

  proof
    wph
    cA
    cB
    cD
    cP
    cA
    cA
    cM
    cfv
    cG
    cmid
    cfv
    #
    co
    cB
    cB
    cM
    cfv
    @0
    co
    @0
    co
    #
    cG
    cmir
    cfv
    cfv
    #
    cG
    cI
    cL
    cM
    c.mi
    @1
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmif.m
    lmif.l
    lmif.d
    lmiiso.1
    lmiiso.2
    @2
    eqid
    @1
    eqid
    lmiisolem
end

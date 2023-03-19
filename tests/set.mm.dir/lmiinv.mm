include "cfv.mm"
include "wceq.mm"
include "cmid.mm"
include "co.mm"
include "wcel.mm"
include "cperpg.mm"
include "wbr.mm"
include "wo.mm"
include "wa.mm"
include "islmib.mm"
include "wb.mm"
include "eqcom.mm"
include "a1i.mm"
include "eqidd.mm"
include "olcd.mm"
include "biantrud.mm"
include "midid.mm"
include "eleq1d.mm"
include "bitr3d.mm"
include "3bitr3d.mm"

theorem lmiinv
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


  assert |- ( ph -> ( ( M ` A ) = A <-> A e. D ) )

  proof
    wph
    cA
    cA
    cM
    cfv
    #
    wceq
    #
    cA
    cA
    cG
    cmid
    cfv
    co
    #
    cD
    wcel
    #
    cD
    cA
    cA
    cL
    co
    cG
    cperpg
    cfv
    wbr
    #
    cA
    cA
    wceq
    #
    wo
    #
    wa
    #
    @0
    cA
    wceq
    #
    cA
    cD
    wcel
    #
    wph
    cA
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
    lmicl.1
    islmib
    @1
    @8
    wb
    wph
    cA
    @0
    eqcom
    a1i
    wph
    @3
    @7
    @9
    wph
    @6
    @3
    wph
    @5
    @4
    wph
    cA
    eqidd
    olcd
    biantrud
    wph
    @2
    cA
    cD
    wph
    cA
    cA
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    lmicl.1
    lmicl.1
    midid
    eleq1d
    bitr3d
    3bitr3d
end

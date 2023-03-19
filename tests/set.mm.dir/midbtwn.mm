include "cmid.mm"
include "cfv.mm"
include "co.mm"
include "midcl.mm"
include "cmir.mm"
include "clng.mm"
include "eqid.mm"
include "mirbtwn.mm"
include "wceq.mm"
include "eqidd.mm"
include "ismidb.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "eleqtrrd.mm"
include "tgbtwncom.mm"

theorem midbtwn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let cL: class L
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume midcl.1: |- ( ph -> A e. P )
  assume midcl.2: |- ( ph -> B e. P )


  assert |- ( ph -> ( A ( midG ` G ) B ) e. ( A I B ) )

  proof
    wph
    cB
    cA
    cB
    cG
    cmid
    cfv
    co
    #
    cA
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    midcl.2
    wph
    cA
    cB
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.1
    midcl.2
    midcl
    #
    midcl.1
    wph
    @0
    cA
    @0
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    cA
    cI
    co
    cB
    cA
    cI
    co
    wph
    @0
    cA
    cP
    @2
    cG
    cI
    cG
    clng
    cfv
    #
    @3
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @5
    eqid
    @2
    eqid
    #
    ismid.g
    @1
    @3
    eqid
    midcl.1
    mirbtwn
    wph
    cB
    @4
    cA
    cI
    wph
    cB
    @4
    wceq
    @0
    @0
    wceq
    wph
    @0
    eqidd
    wph
    cA
    cB
    cP
    @2
    cG
    cI
    @0
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.1
    midcl.2
    @6
    @1
    ismidb
    mpbird
    oveq1d
    eleqtrrd
    tgbtwncom
end

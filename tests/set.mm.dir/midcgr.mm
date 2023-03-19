include "co.mm"
include "cmir.mm"
include "cfv.mm"
include "wceq.mm"
include "cmid.mm"
include "eqid.mm"
include "midcl.mm"
include "eqeltrrd.mm"
include "ismidb.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "clng.mm"
include "mircgr.mm"
include "eqtr2d.mm"

theorem midcgr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume midcgr.1: |- ( ph -> ( A ( midG ` G ) B ) = C )


  assert |- ( ph -> ( C .- A ) = ( C .- B ) )

  proof
    wph
    cC
    cB
    c.mi
    co
    cC
    cA
    cC
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    #
    c.mi
    co
    cC
    cA
    c.mi
    co
    wph
    cB
    @2
    cC
    c.mi
    wph
    cB
    @2
    wceq
    cA
    cB
    cG
    cmid
    cfv
    co
    #
    cC
    wceq
    midcgr.1
    wph
    cA
    cB
    cP
    @0
    cG
    cI
    cC
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.1
    midcl.2
    @0
    eqid
    #
    wph
    @3
    cC
    cP
    midcgr.1
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
    eqeltrrd
    #
    ismidb
    mpbird
    oveq2d
    wph
    cC
    cA
    cP
    @0
    cG
    cI
    cG
    clng
    cfv
    #
    @1
    c.mi
    ismid.p
    ismid.d
    ismid.i
    @6
    eqid
    @4
    ismid.g
    @5
    @1
    eqid
    midcl.1
    mircgr
    eqtr2d
end

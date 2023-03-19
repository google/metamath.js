include "cmid.mm"
include "cfv.mm"
include "co.mm"
include "cmir.mm"
include "wceq.mm"
include "clng.mm"
include "eqid.mm"
include "midcl.mm"
include "eqidd.mm"
include "midcgr.mm"
include "midbtwn.mm"
include "ismir.mm"
include "ismidb.mm"
include "mpbid.mm"

theorem midcom
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


  assert |- ( ph -> ( A ( midG ` G ) B ) = ( B ( midG ` G ) A ) )

  proof
    wph
    cB
    cA
    cB
    cA
    cG
    cmid
    cfv
    #
    co
    #
    cG
    cmir
    cfv
    #
    cfv
    #
    cfv
    wceq
    cA
    cB
    @0
    co
    @1
    wceq
    wph
    @1
    cA
    cB
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
    @4
    eqid
    @2
    eqid
    #
    ismid.g
    wph
    cB
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
    midcl.2
    midcl.1
    midcl
    #
    @3
    eqid
    midcl.1
    midcl.2
    wph
    cB
    cA
    @1
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.2
    midcl.1
    wph
    @1
    eqidd
    midcgr
    wph
    cB
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
    midcl.2
    midcl.1
    midbtwn
    ismir
    wph
    cA
    cB
    cP
    @2
    cG
    cI
    @1
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.1
    midcl.2
    @5
    @6
    ismidb
    mpbid
end

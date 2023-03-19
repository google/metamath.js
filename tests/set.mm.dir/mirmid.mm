include "cfv.mm"
include "cmid.mm"
include "co.mm"
include "cmir.mm"
include "wceq.mm"
include "eqidd.mm"
include "eqid.mm"
include "midcl.mm"
include "ismidb.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "clng.mm"
include "mirmir2.mm"
include "eqtrd.mm"
include "mircl.mm"
include "mpbid.mm"

theorem mirmid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cG: class G
  let cI: class I
  let cM: class M
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
  assume mirmid.s: |- S = ( ( pInvG ` G ) ` M )
  assume mirmid.x: |- ( ph -> M e. P )


  assert |- ( ph -> ( ( S ` A ) ( midG ` G ) ( S ` B ) ) = ( S ` ( A ( midG ` G ) B ) ) )

  proof
    wph
    cB
    cS
    cfv
    #
    cA
    cS
    cfv
    #
    cA
    cB
    cG
    cmid
    cfv
    #
    co
    #
    cS
    cfv
    #
    cG
    cmir
    cfv
    #
    cfv
    cfv
    #
    wceq
    @1
    @0
    @2
    co
    @4
    wceq
    wph
    @0
    cA
    @3
    @5
    cfv
    cfv
    #
    cS
    cfv
    @6
    wph
    cB
    @7
    cS
    wph
    cB
    @7
    wceq
    @3
    @3
    wceq
    wph
    @3
    eqidd
    wph
    cA
    cB
    cP
    @5
    cG
    cI
    @3
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.1
    midcl.2
    @5
    eqid
    #
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
    ismidb
    mpbird
    fveq2d
    wph
    cM
    cP
    @5
    cG
    cI
    cG
    clng
    cfv
    #
    cS
    c.mi
    cA
    @3
    ismid.p
    ismid.d
    ismid.i
    @10
    eqid
    #
    @8
    ismid.g
    mirmid.x
    mirmid.s
    midcl.1
    @9
    mirmir2
    eqtrd
    wph
    @1
    @0
    cP
    @5
    cG
    cI
    @4
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    wph
    cM
    cP
    @5
    cG
    cI
    @10
    cS
    c.mi
    cA
    ismid.p
    ismid.d
    ismid.i
    @11
    @8
    ismid.g
    mirmid.x
    mirmid.s
    midcl.1
    mircl
    wph
    cM
    cP
    @5
    cG
    cI
    @10
    cS
    c.mi
    cB
    ismid.p
    ismid.d
    ismid.i
    @11
    @8
    ismid.g
    mirmid.x
    mirmid.s
    midcl.2
    mircl
    @8
    wph
    cM
    cP
    @5
    cG
    cI
    @10
    cS
    c.mi
    @3
    ismid.p
    ismid.d
    ismid.i
    @11
    @8
    ismid.g
    mirmid.x
    mirmid.s
    @9
    mircl
    ismidb
    mpbid
end

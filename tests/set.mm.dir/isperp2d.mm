include "cv.mm"
include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cperpg.mm"
include "wbr.mm"
include "isperp2.mm"
include "mpbid.mm"
include "wi.mm"
include "wceq.mm"
include "id.mm"
include "eqidd.mm"
include "s3eqd.mm"
include "eleq1d.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mpd.mm"

theorem isperp2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume isperp2.b: |- ( ph -> B e. ran L )
  assume isperp2.x: |- ( ph -> X e. ( A i^i B ) )
  assume isperp2d.u: |- ( ph -> U e. A )
  assume isperp2d.v: |- ( ph -> V e. B )
  assume isperp2d.p: |- ( ph -> A ( perpG ` G ) B )


  assert |- ( ph -> <" U X V "> e. ( raG ` G ) )

  proof
    wph
    vu
    cv
    #
    cX
    vv
    cv
    #
    cs3
    #
    cG
    crag
    cfv
    #
    wcel
    #
    vv
    cB
    wral
    vu
    cA
    wral
    #
    cU
    cX
    cV
    cs3
    #
    @3
    wcel
    #
    wph
    cA
    cB
    cG
    cperpg
    cfv
    wbr
    @5
    isperp2d.p
    wph
    vv
    vu
    cA
    cB
    cP
    cG
    cI
    cL
    c.mi
    cX
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    isperp.a
    isperp2.b
    isperp2.x
    isperp2
    mpbid
    wph
    cU
    cA
    wcel
    cV
    cB
    wcel
    @5
    @7
    wi
    isperp2d.u
    isperp2d.v
    @4
    @7
    cU
    cX
    @1
    cs3
    #
    @3
    wcel
    vu
    vv
    cU
    cV
    cA
    cB
    @0
    cU
    wceq
    #
    @2
    @8
    @3
    @9
    @0
    cX
    @1
    @1
    cU
    cX
    @9
    id
    @9
    cX
    eqidd
    @9
    @1
    eqidd
    s3eqd
    eleq1d
    @1
    cV
    wceq
    #
    @8
    @6
    @3
    @10
    cU
    cX
    @1
    cV
    cU
    cX
    @10
    cU
    eqidd
    @10
    cX
    eqidd
    @10
    id
    s3eqd
    eleq1d
    rspc2v
    syl2anc
    mpd
end

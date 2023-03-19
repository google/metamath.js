include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "cple.mm"
include "eqid.mm"
include "ipobas.mm"
include "cglb.mm"
include "wceq.mm"
include "a1i.mm"
include "cpo.mm"
include "ipopos.mm"
include "wss.mm"
include "0ss.mm"
include "mre1cl.mm"
include "cv.mm"
include "wbr.mm"
include "ral0.mm"
include "rspec.mm"
include "adantl.mm"
include "wral.mm"
include "wa.mm"
include "mress.mm"
include "wb.mm"
include "adantr.mm"
include "ipole.mm"
include "mpd3an3.mm"
include "mpbird.mm"
include "3adant3.mm"
include "posglbd.mm"

theorem mrelatglb0
  let cC: class C
  let cG: class G
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cL: class L
  let cU: class U
  let cF: class F
  assume mreclat.i: |- I = ( toInc ` C )
  assume mrelatglb.g: |- G = ( glb ` I )


  assert |- ( C e. ( Moore ` X ) -> ( G ` (/) ) = X )

  proof
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    vx
    vy
    cC
    c0
    cX
    cG
    cI
    cI
    cple
    cfv
    #
    @2
    eqid
    #
    cC
    cI
    @0
    mreclat.i
    ipobas
    cG
    cI
    cglb
    cfv
    wceq
    @1
    mrelatglb.g
    a1i
    cI
    cpo
    wcel
    @1
    cC
    cI
    mreclat.i
    ipopos
    a1i
    c0
    cC
    wss
    @1
    cC
    0ss
    a1i
    cC
    cX
    mre1cl
    #
    vx
    cv
    #
    c0
    wcel
    cX
    @5
    @2
    wbr
    #
    @1
    @6
    vx
    c0
    @6
    vx
    ral0
    rspec
    adantl
    @1
    vy
    cv
    #
    cC
    wcel
    #
    @7
    cX
    @2
    wbr
    #
    @7
    @5
    @2
    wbr
    vx
    c0
    wral
    @1
    @8
    wa
    @9
    @7
    cX
    wss
    #
    cC
    @7
    cX
    mress
    @1
    @8
    cX
    cC
    wcel
    #
    @9
    @10
    wb
    @1
    @11
    @8
    @4
    adantr
    cC
    cI
    @2
    @0
    @7
    cX
    mreclat.i
    @3
    ipole
    mpd3an3
    mpbird
    3adant3
    posglbd
end

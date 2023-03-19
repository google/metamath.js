include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wrel.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "cint.mm"
include "ccnv.mm"
include "cvv.mm"
include "wcel.mm"
include "cnvexg.mm"
include "3syl.mm"
include "wceq.mm"
include "dfrel2.mm"
include "sylib.mm"
include "cnvss.mm"
include "eqsstr3d.mm"
include "relcnv.mm"
include "a1i.mm"
include "jca31.mm"
include "cleq2lem.mm"
include "releq.mm"
include "anbi12d.mm"
include "elabd.mm"
include "rexab2.mm"
include "biimpri.mm"
include "relint.mm"

theorem clrellem
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume clrellem.y: |- ( ph -> Y e. _V )
  assume clrellem.rel: |- ( ph -> Rel X )
  assume clrellem.sub: |- ( x = `' `' Y -> ( ps <-> ch ) )
  assume clrellem.sup: |- ( ph -> X C_ Y )
  assume clrellem.maj: |- ( ph -> ch )

  disjoint X x
  disjoint Y x
  disjoint ph x
  disjoint ch x
  disjoint x y
  disjoint X y
  disjoint ps y
  assert |- ( ph -> Rel |^| { x | ( X C_ x /\ ps ) } )

  proof
    wph
    cX
    vx
    cv
    #
    wss
    wps
    wa
    #
    @0
    wrel
    #
    wa
    #
    vx
    wex
    #
    vy
    cv
    #
    wrel
    #
    vy
    @1
    vx
    cab
    #
    wrex
    #
    @7
    cint
    wrel
    wph
    @3
    cX
    cY
    ccnv
    #
    ccnv
    #
    wss
    #
    wch
    wa
    #
    @10
    wrel
    #
    wa
    vx
    @10
    wph
    cY
    cvv
    wcel
    @9
    cvv
    wcel
    @10
    cvv
    wcel
    clrellem.y
    cY
    cvv
    cnvexg
    @9
    cvv
    cnvexg
    3syl
    wph
    @11
    wch
    @13
    wph
    cX
    cX
    ccnv
    #
    ccnv
    #
    @10
    wph
    cX
    wrel
    @15
    cX
    wceq
    clrellem.rel
    cX
    dfrel2
    sylib
    wph
    cX
    cY
    wss
    @14
    @9
    wss
    @15
    @10
    wss
    clrellem.sup
    cX
    cY
    cnvss
    @14
    @9
    cnvss
    3syl
    eqsstr3d
    clrellem.maj
    @13
    wph
    @9
    relcnv
    a1i
    jca31
    @0
    @10
    wceq
    @1
    @12
    @2
    @13
    wps
    wch
    @0
    @10
    cX
    clrellem.sub
    cleq2lem
    @0
    @10
    releq
    anbi12d
    elabd
    @8
    @4
    @1
    @6
    @2
    vy
    vx
    @5
    @0
    releq
    rexab2
    biimpri
    vy
    @7
    relint
    3syl
end

include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmin.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wral.mm"
include "wcel.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "ltsubrpd.mm"
include "wb.mm"
include "rpred.mm"
include "resubcld.mm"
include "suprlub.mm"
include "syl31anc.mm"
include "mpbid.mm"

theorem suprltrp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cX: class X
  assume suprltrp.a: |- ( ph -> A C_ RR )
  assume suprltrp.n0: |- ( ph -> A =/= (/) )
  assume suprltrp.bnd: |- ( ph -> E. x e. RR A. y e. A y <_ x )
  assume suprltrp.x: |- ( ph -> X e. RR+ )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint X z
  assert |- ( ph -> E. z e. A ( sup ( A , RR , < ) - X ) < z )

  proof
    wph
    cA
    cr
    clt
    csup
    #
    cX
    cmin
    co
    #
    @0
    clt
    wbr
    #
    @1
    vz
    cv
    clt
    wbr
    vz
    cA
    wrex
    #
    wph
    @0
    cX
    wph
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    #
    @0
    cr
    wcel
    suprltrp.a
    suprltrp.n0
    suprltrp.bnd
    vx
    vy
    cA
    suprcl
    syl3anc
    #
    suprltrp.x
    ltsubrpd
    wph
    @4
    @5
    @6
    @1
    cr
    wcel
    @2
    @3
    wb
    suprltrp.a
    suprltrp.n0
    suprltrp.bnd
    wph
    @0
    cX
    @7
    wph
    cX
    suprltrp.x
    rpred
    resubcld
    vx
    vy
    vz
    cA
    @1
    suprlub
    syl31anc
    mpbid
end

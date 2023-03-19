include "chomf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "wral.mm"
include "cbs.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "eqid.mm"
include "homffval.mm"
include "syl6reqr.mm"
include "eqeq12d.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "ovex.mm"
include "rgen2w.mm"
include "mpt22eqb.mm"
include "ax-mp.mm"
include "syl6bb.mm"

theorem homfeq
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cH: class H
  let cJ: class J
  assume homfeq.h: |- H = ( Hom ` C )
  assume homfeq.j: |- J = ( Hom ` D )
  assume homfeq.1: |- ( ph -> B = ( Base ` C ) )
  assume homfeq.2: |- ( ph -> B = ( Base ` D ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint H x
  disjoint H y
  disjoint ph x
  disjoint ph y
  disjoint J x
  disjoint J y
  assert |- ( ph -> ( ( Homf ` C ) = ( Homf ` D ) <-> A. x e. B A. y e. B ( x H y ) = ( x J y ) ) )

  proof
    wph
    cC
    chomf
    cfv
    #
    cD
    chomf
    cfv
    #
    wceq
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    cmpt2
    #
    vx
    vy
    cB
    cB
    @2
    @3
    cJ
    co
    #
    cmpt2
    #
    wceq
    #
    @4
    @6
    wceq
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wph
    @0
    @5
    @1
    @7
    wph
    @5
    vx
    vy
    cC
    cbs
    cfv
    #
    @10
    @4
    cmpt2
    @0
    wph
    vx
    vy
    cB
    cB
    @4
    @10
    @10
    @4
    homfeq.1
    homfeq.1
    wph
    @4
    eqidd
    mpt2eq123dv
    vx
    vy
    @10
    cC
    @0
    cH
    @0
    eqid
    @10
    eqid
    homfeq.h
    homffval
    syl6reqr
    wph
    @7
    vx
    vy
    cD
    cbs
    cfv
    #
    @11
    @6
    cmpt2
    @1
    wph
    vx
    vy
    cB
    cB
    @6
    @11
    @11
    @6
    homfeq.2
    homfeq.2
    wph
    @6
    eqidd
    mpt2eq123dv
    vx
    vy
    @11
    cD
    @1
    cJ
    @1
    eqid
    @11
    eqid
    homfeq.j
    homffval
    syl6reqr
    eqeq12d
    @4
    cvv
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @8
    @9
    wb
    @12
    vx
    vy
    cB
    cB
    @2
    @3
    cH
    ovex
    rgen2w
    vx
    vy
    cB
    cB
    @4
    @6
    cvv
    mpt22eqb
    ax-mp
    syl6bb
end

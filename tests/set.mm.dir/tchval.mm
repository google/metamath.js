include "ctch.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "ctng.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "cip.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "mpteq12dv.mm"
include "oveq12d.mm"
include "df-tch.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "reldmtng.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem tchval
  let vx: setvar x
  let cG: class G
  let c.xi: class .,
  let cV: class V
  let cW: class W
  let c.mi: class .-
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cC: class C
  let wph: wff ph
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchval.v: |- V = ( Base ` W )
  assume tchval.h: |- ., = ( .i ` W )

  disjoint ., x
  disjoint G x
  disjoint V x
  disjoint W x
  disjoint .- x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ., w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ., y
  disjoint ., z
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G y
  disjoint G z
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint C x
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint W w
  disjoint W y
  disjoint W z
  disjoint .x. x
  disjoint X x
  disjoint Y x
  assert |- G = ( W toNrmGrp ( x e. V |-> ( sqrt ` ( x ., x ) ) ) )

  proof
    cG
    cW
    ctch
    cfv
    #
    cW
    vx
    cV
    vx
    cv
    #
    @1
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    ctng
    co
    #
    tchval.n
    cW
    cvv
    wcel
    #
    @0
    @5
    wceq
    vw
    cW
    vw
    cv
    #
    vx
    @7
    cbs
    cfv
    #
    @1
    @1
    @7
    cip
    cfv
    #
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    ctng
    co
    @5
    cvv
    ctch
    @7
    cW
    wceq
    #
    @7
    cW
    @12
    @4
    ctng
    @13
    id
    @13
    vx
    @8
    @11
    cV
    @3
    @13
    @8
    cW
    cbs
    cfv
    cV
    @7
    cW
    cbs
    fveq2
    tchval.v
    syl6eqr
    @13
    @10
    @2
    csqrt
    @13
    @9
    c.xi
    @1
    @1
    @13
    @9
    cW
    cip
    cfv
    c.xi
    @7
    cW
    cip
    fveq2
    tchval.h
    syl6eqr
    oveqd
    fveq2d
    mpteq12dv
    oveq12d
    vx
    vw
    df-tch
    cW
    @4
    ctng
    ovex
    fvmpt
    @6
    wn
    @0
    c0
    @5
    cW
    ctch
    fvprc
    cW
    @4
    ctng
    reldmtng
    ovprc1
    eqtr4d
    pm2.61i
    eqtri
end

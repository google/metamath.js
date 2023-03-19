include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "tgbtwntriv1.mm"
include "tgcgrtriv.mm"
include "eleq1.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "legov.mm"
include "mpbird.mm"

theorem leg0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let cF: class F
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legid.a: |- ( ph -> A e. P )
  assume legid.b: |- ( ph -> B e. P )
  assume legtrd.c: |- ( ph -> C e. P )
  assume legtrd.d: |- ( ph -> D e. P )


  assert |- ( ph -> ( A .- A ) .<_ ( C .- D ) )

  proof
    wph
    cA
    cA
    c.mi
    co
    #
    cC
    cD
    c.mi
    co
    c.le
    wbr
    vx
    cv
    #
    cC
    cD
    cI
    co
    #
    wcel
    #
    @0
    cC
    @1
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vx
    cP
    wrex
    #
    wph
    cC
    cP
    wcel
    cC
    @2
    wcel
    #
    @0
    cC
    cC
    c.mi
    co
    #
    wceq
    #
    @7
    legtrd.c
    wph
    cC
    cD
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    legval.g
    legtrd.c
    legtrd.d
    tgbtwntriv1
    wph
    cA
    cC
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    legval.g
    legid.a
    legtrd.c
    tgcgrtriv
    @6
    @8
    @10
    wa
    vx
    cC
    cP
    @1
    cC
    wceq
    #
    @3
    @8
    @5
    @10
    @1
    cC
    @2
    eleq1
    @11
    @4
    @9
    @0
    @1
    cC
    cC
    c.mi
    oveq2
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    wph
    vx
    cA
    cA
    cC
    cD
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legid.a
    legid.a
    legtrd.c
    legtrd.d
    legov
    mpbird
end

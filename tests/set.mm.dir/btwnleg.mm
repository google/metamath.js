include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "eqidd.mm"
include "eleq1.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "legov.mm"
include "mpbird.mm"

theorem btwnleg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
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
  assume btwnleg.1: |- ( ph -> B e. ( A I C ) )


  assert |- ( ph -> ( A .- B ) .<_ ( A .- C ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    #
    cA
    cC
    c.mi
    co
    c.le
    wbr
    vx
    cv
    #
    cA
    cC
    cI
    co
    #
    wcel
    #
    @0
    cA
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
    cB
    cP
    wcel
    cB
    @2
    wcel
    #
    @0
    @0
    wceq
    #
    @7
    legid.b
    btwnleg.1
    wph
    @0
    eqidd
    @6
    @8
    @9
    wa
    vx
    cB
    cP
    @1
    cB
    wceq
    #
    @3
    @8
    @5
    @9
    @1
    cB
    @2
    eleq1
    @10
    @4
    @0
    @0
    @1
    cB
    cA
    c.mi
    oveq2
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    wph
    vx
    cA
    cB
    cA
    cC
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
    legid.b
    legid.a
    legtrd.c
    legov
    mpbird
end

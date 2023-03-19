include "co.mm"
include "wceq.mm"
include "cs3.mm"
include "wbr.mm"
include "w3a.mm"
include "trgcgrg.mm"
include "mpbid.mm"
include "simp2d.mm"

theorem cgr3simp2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let c.sm: class .~
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  assume tgcgrxfr.p: |- P = ( Base ` G )
  assume tgcgrxfr.m: |- .- = ( dist ` G )
  assume tgcgrxfr.i: |- I = ( Itv ` G )
  assume tgcgrxfr.r: |- .~ = ( cgrG ` G )
  assume tgcgrxfr.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnxfr.a: |- ( ph -> A e. P )
  assume tgbtwnxfr.b: |- ( ph -> B e. P )
  assume tgbtwnxfr.c: |- ( ph -> C e. P )
  assume tgbtwnxfr.d: |- ( ph -> D e. P )
  assume tgbtwnxfr.e: |- ( ph -> E e. P )
  assume tgbtwnxfr.f: |- ( ph -> F e. P )
  assume tgbtwnxfr.2: |- ( ph -> <" A B C "> .~ <" D E F "> )


  assert |- ( ph -> ( B .- C ) = ( E .- F ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
    wceq
    #
    cB
    cC
    c.mi
    co
    cE
    cF
    c.mi
    co
    wceq
    #
    cC
    cA
    c.mi
    co
    cF
    cD
    c.mi
    co
    wceq
    #
    wph
    cA
    cB
    cC
    cs3
    cD
    cE
    cF
    cs3
    c.sm
    wbr
    @0
    @1
    @2
    w3a
    tgbtwnxfr.2
    wph
    cA
    cB
    cC
    cD
    cP
    c.sm
    cE
    cF
    cG
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    trgcgrg
    mpbid
    simp2d
end

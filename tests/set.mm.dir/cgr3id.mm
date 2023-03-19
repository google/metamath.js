include "co.mm"
include "eqidd.mm"
include "trgcgr.mm"

theorem cgr3id
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cD: class D
  let cF: class F
  assume tgcgrxfr.p: |- P = ( Base ` G )
  assume tgcgrxfr.m: |- .- = ( dist ` G )
  assume tgcgrxfr.i: |- I = ( Itv ` G )
  assume tgcgrxfr.r: |- .~ = ( cgrG ` G )
  assume tgcgrxfr.g: |- ( ph -> G e. TarskiG )
  assume tgbtwnxfr.a: |- ( ph -> A e. P )
  assume tgbtwnxfr.b: |- ( ph -> B e. P )
  assume tgbtwnxfr.c: |- ( ph -> C e. P )


  assert |- ( ph -> <" A B C "> .~ <" A B C "> )

  proof
    wph
    cA
    cB
    cC
    cA
    cP
    c.sm
    cB
    cC
    cG
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    wph
    cA
    cB
    c.mi
    co
    eqidd
    wph
    cB
    cC
    c.mi
    co
    eqidd
    wph
    cC
    cA
    c.mi
    co
    eqidd
    trgcgr
end

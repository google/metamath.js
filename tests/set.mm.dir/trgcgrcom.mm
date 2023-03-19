include "co.mm"
include "cgr3simp1.mm"
include "eqcomd.mm"
include "cgr3simp2.mm"
include "cgr3simp3.mm"
include "trgcgr.mm"

theorem trgcgrcom
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


  assert |- ( ph -> <" D E F "> .~ <" A B C "> )

  proof
    wph
    cD
    cE
    cF
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
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    wph
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
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
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    tgbtwnxfr.2
    cgr3simp1
    eqcomd
    wph
    cB
    cC
    c.mi
    co
    cE
    cF
    c.mi
    co
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
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    tgbtwnxfr.2
    cgr3simp2
    eqcomd
    wph
    cC
    cA
    c.mi
    co
    cF
    cD
    c.mi
    co
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
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    tgbtwnxfr.2
    cgr3simp3
    eqcomd
    trgcgr
end

include "cgr3simp1.mm"
include "tgcgrcomlr.mm"
include "cgr3simp3.mm"
include "cgr3simp2.mm"
include "trgcgr.mm"

theorem cgr3swap12
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


  assert |- ( ph -> <" B A C "> .~ <" E D F "> )

  proof
    wph
    cB
    cA
    cC
    cE
    cP
    c.sm
    cD
    cF
    cG
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.b
    tgbtwnxfr.a
    tgbtwnxfr.c
    tgbtwnxfr.e
    tgbtwnxfr.d
    tgbtwnxfr.f
    wph
    cA
    cB
    cD
    cE
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.g
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.d
    tgbtwnxfr.e
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
    tgcgrcomlr
    wph
    cC
    cA
    cF
    cD
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.g
    tgbtwnxfr.c
    tgbtwnxfr.a
    tgbtwnxfr.f
    tgbtwnxfr.d
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
    tgcgrcomlr
    wph
    cB
    cC
    cE
    cF
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.g
    tgbtwnxfr.b
    tgbtwnxfr.c
    tgbtwnxfr.e
    tgbtwnxfr.f
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
    tgcgrcomlr
    trgcgr
end

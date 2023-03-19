include "co.mm"
include "cgr3simp1.mm"
include "eqtrd.mm"
include "cgr3simp2.mm"
include "cgr3simp3.mm"
include "trgcgr.mm"

theorem cgr3tr
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
  let cJ: class J
  let cK: class K
  let cL: class L
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
  assume cgr3tr.j: |- ( ph -> J e. P )
  assume cgr3tr.k: |- ( ph -> K e. P )
  assume cgr3tr.l: |- ( ph -> L e. P )
  assume cgr3tr.1: |- ( ph -> <" D E F "> .~ <" J K L "> )


  assert |- ( ph -> <" A B C "> .~ <" J K L "> )

  proof
    wph
    cA
    cB
    cC
    cJ
    cP
    c.sm
    cK
    cL
    cG
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.a
    tgbtwnxfr.b
    tgbtwnxfr.c
    cgr3tr.j
    cgr3tr.k
    cgr3tr.l
    wph
    cA
    cB
    c.mi
    co
    cD
    cE
    c.mi
    co
    cJ
    cK
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
    wph
    cD
    cE
    cF
    cJ
    cP
    c.sm
    cK
    cL
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    cgr3tr.j
    cgr3tr.k
    cgr3tr.l
    cgr3tr.1
    cgr3simp1
    eqtrd
    wph
    cB
    cC
    c.mi
    co
    cE
    cF
    c.mi
    co
    cK
    cL
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
    wph
    cD
    cE
    cF
    cJ
    cP
    c.sm
    cK
    cL
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    cgr3tr.j
    cgr3tr.k
    cgr3tr.l
    cgr3tr.1
    cgr3simp2
    eqtrd
    wph
    cC
    cA
    c.mi
    co
    cF
    cD
    c.mi
    co
    cL
    cJ
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
    wph
    cD
    cE
    cF
    cJ
    cP
    c.sm
    cK
    cL
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    tgcgrxfr.g
    tgbtwnxfr.d
    tgbtwnxfr.e
    tgbtwnxfr.f
    cgr3tr.j
    cgr3tr.k
    cgr3tr.l
    cgr3tr.1
    cgr3simp3
    eqtrd
    trgcgr
end

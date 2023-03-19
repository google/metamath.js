include "cv.mm"
include "co.mm"
include "wcel.mm"
include "cs3.mm"
include "wbr.mm"
include "wa.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "simprl.mm"
include "eqidd.mm"
include "simprr.mm"
include "trgcgrcom.mm"
include "cgr3tr.mm"
include "cgr3simp1.mm"
include "cgr3simp2.mm"
include "tgcgrcomlr.mm"
include "tgifscgr.mm"
include "axtgcgrid.mm"
include "eqeltrrd.mm"
include "cgr3simp3.mm"
include "tgcgrxfr.mm"
include "r19.29a.mm"

theorem tgbtwnxfr
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
  assume tgbtwnxfr.1: |- ( ph -> B e. ( A I C ) )


  assert |- ( ph -> E e. ( D I F ) )

  proof
    wph
    ve
    cv
    #
    cD
    cF
    cI
    co
    #
    wcel
    #
    cA
    cB
    cC
    cs3
    #
    cD
    @0
    cF
    cs3
    c.sm
    wbr
    #
    wa
    #
    cE
    @1
    wcel
    ve
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @5
    wa
    #
    @0
    cE
    @1
    @8
    cP
    cG
    cI
    c.mi
    @0
    cE
    @0
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    wph
    cG
    cstrkg
    wcel
    @6
    @5
    tgcgrxfr.g
    ad2antrr
    #
    wph
    @6
    @5
    simplr
    #
    wph
    cE
    cP
    wcel
    @6
    @5
    tgbtwnxfr.e
    ad2antrr
    #
    @10
    @8
    cD
    @0
    cF
    cE
    cP
    cD
    @0
    cG
    @0
    cI
    cF
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @9
    wph
    cD
    cP
    wcel
    @6
    @5
    tgbtwnxfr.d
    ad2antrr
    #
    @10
    wph
    cF
    cP
    wcel
    @6
    @5
    tgbtwnxfr.f
    ad2antrr
    #
    @11
    @12
    @10
    @13
    @10
    @7
    @2
    @4
    simprl
    #
    @14
    @8
    cD
    cF
    c.mi
    co
    eqidd
    @8
    @0
    cF
    c.mi
    co
    eqidd
    @8
    cD
    cE
    cF
    cD
    cP
    c.sm
    @0
    cF
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    @9
    @12
    @11
    @13
    @12
    @10
    @13
    @8
    cD
    @0
    cF
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
    @9
    @12
    @10
    @13
    @12
    @11
    @13
    @8
    cD
    @0
    cF
    cA
    cP
    c.sm
    cB
    cC
    cG
    cI
    cD
    cE
    cF
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    @9
    @12
    @10
    @13
    wph
    cA
    cP
    wcel
    @6
    @5
    tgbtwnxfr.a
    ad2antrr
    #
    wph
    cB
    cP
    wcel
    @6
    @5
    tgbtwnxfr.b
    ad2antrr
    #
    wph
    cC
    cP
    wcel
    @6
    @5
    tgbtwnxfr.c
    ad2antrr
    #
    @8
    cA
    cB
    cC
    cD
    cP
    c.sm
    @0
    cF
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    @9
    @15
    @16
    @17
    @12
    @10
    @13
    @7
    @2
    @4
    simprr
    trgcgrcom
    @12
    @11
    @13
    wph
    @3
    cD
    cE
    cF
    cs3
    c.sm
    wbr
    @6
    @5
    tgbtwnxfr.2
    ad2antrr
    cgr3tr
    trgcgrcom
    #
    cgr3simp1
    @8
    cE
    cF
    @0
    cF
    cP
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    @9
    @11
    @13
    @10
    @13
    @8
    cD
    cE
    cF
    cD
    cP
    c.sm
    @0
    cF
    cG
    cI
    c.mi
    tgcgrxfr.p
    tgcgrxfr.m
    tgcgrxfr.i
    tgcgrxfr.r
    @9
    @12
    @11
    @13
    @12
    @10
    @13
    @18
    cgr3simp2
    tgcgrcomlr
    tgifscgr
    axtgcgrid
    @14
    eqeltrrd
    wph
    cA
    cB
    cC
    cD
    cP
    c.sm
    ve
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
    tgbtwnxfr.f
    tgbtwnxfr.1
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
    tgcgrxfr
    r19.29a
end

include "cqg.mm"
include "co.mm"
include "cqs.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cmpt2.mm"
include "eqid.mm"
include "weq.mm"
include "oveq2.mm"
include "cbvmptv.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "mpteq1.mm"
include "cbvmpt2v.mm"
include "sylow2blem3.mm"

theorem sylow2b
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let c.pl: class .+
  let vg: setvar g
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let c.x: class .x.
  let c.sm: class .~
  let cB: class B
  let cC: class C
  assume sylow2b.x: |- X = ( Base ` G )
  assume sylow2b.xf: |- ( ph -> X e. Fin )
  assume sylow2b.h: |- ( ph -> H e. ( SubGrp ` G ) )
  assume sylow2b.k: |- ( ph -> K e. ( SubGrp ` G ) )
  assume sylow2b.a: |- .+ = ( +g ` G )
  assume sylow2b.hp: |- ( ph -> P pGrp ( G |`s H ) )
  assume sylow2b.kn: |- ( ph -> ( # ` K ) = ( P ^ ( P pCnt ( # ` X ) ) ) )
  assume sylow2b.d: |- .- = ( -g ` G )

  disjoint g x
  disjoint G g
  disjoint G x
  disjoint K g
  disjoint K x
  disjoint .+ g
  disjoint .+ x
  disjoint g ph
  disjoint .- x
  disjoint H g
  disjoint H x
  disjoint X g
  disjoint X x
  disjoint a b
  disjoint a g
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint G a
  disjoint b g
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint G b
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint g z
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint K u
  disjoint K v
  disjoint K y
  disjoint K z
  disjoint .x. a
  disjoint .x. b
  disjoint .x. g
  disjoint .x. s
  disjoint .x. u
  disjoint .x. v
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .+ s
  disjoint .+ u
  disjoint .+ v
  disjoint .+ y
  disjoint .+ z
  disjoint .~ a
  disjoint .~ b
  disjoint .~ g
  disjoint .~ s
  disjoint .~ u
  disjoint .~ v
  disjoint .~ x
  disjoint .~ y
  disjoint .~ z
  disjoint a ph
  disjoint b ph
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph z
  disjoint .- u
  disjoint .- z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H a
  disjoint H b
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H y
  disjoint H z
  disjoint X a
  disjoint X b
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X y
  disjoint X z
  assert |- ( ph -> E. g e. X H C_ ran ( x e. K |-> ( ( g .+ x ) .- g ) ) )

  proof
    wph
    vx
    vy
    vz
    cP
    c.pl
    cG
    cK
    cqg
    co
    #
    vu
    vv
    cH
    cX
    @0
    cqs
    #
    vs
    vv
    cv
    #
    vu
    cv
    #
    vs
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    crn
    #
    cmpt2
    vg
    cG
    cH
    cK
    c.mi
    cX
    sylow2b.x
    sylow2b.xf
    sylow2b.h
    sylow2b.k
    sylow2b.a
    @0
    eqid
    vu
    vv
    vx
    vy
    cH
    @1
    @7
    vz
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    cmpt
    #
    crn
    vz
    @2
    @11
    cmpt
    #
    crn
    vu
    vx
    weq
    #
    @6
    @13
    @14
    @6
    vz
    @2
    @3
    @10
    c.pl
    co
    #
    cmpt
    @13
    vs
    vz
    @2
    @5
    @15
    @4
    @10
    @3
    c.pl
    oveq2
    cbvmptv
    @14
    vz
    @2
    @15
    @11
    @3
    @9
    @10
    c.pl
    oveq1
    mpteq2dv
    syl5eq
    rneqd
    vv
    vy
    weq
    @13
    @12
    vz
    @2
    @8
    @11
    mpteq1
    rneqd
    cbvmpt2v
    sylow2b.hp
    sylow2b.kn
    sylow2b.d
    sylow2blem3
end

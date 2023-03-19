include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmpt.mm"
include "cfv.mm"
include "nfmpt1.mm"
include "eqid.mm"
include "fmptdf.mm"
include "limsupubuz.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "a1i.mm"
include "fvmpt2d.mm"
include "breq1d.mm"
include "ralbida.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "breq2.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "sylib.mm"

theorem limsupubuzmpt
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vj: setvar j
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume limsupubuzmpt.j: |- F/ j ph
  assume limsupubuzmpt.z: |- Z = ( ZZ>= ` M )
  assume limsupubuzmpt.b: |- ( ( ph /\ j e. Z ) -> B e. RR )
  assume limsupubuzmpt.n: |- ( ph -> ( limsup ` ( j e. Z |-> B ) ) =/= +oo )

  disjoint B x
  disjoint M j
  disjoint Z j
  disjoint Z x
  disjoint j x
  disjoint B y
  disjoint x y
  disjoint M y
  disjoint j y
  disjoint Z y
  disjoint ph y
  assert |- ( ph -> E. x e. RR A. j e. Z B <_ x )

  proof
    wph
    cB
    vy
    cv
    #
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    cB
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    wph
    vj
    cv
    #
    vj
    cZ
    cB
    cmpt
    #
    cfv
    #
    @0
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vy
    cr
    wrex
    @3
    wph
    vy
    vj
    @8
    cM
    cZ
    vj
    cZ
    cB
    nfmpt1
    limsupubuzmpt.z
    wph
    vj
    cZ
    cB
    cr
    @8
    limsupubuzmpt.j
    limsupubuzmpt.b
    @8
    eqid
    #
    fmptdf
    limsupubuzmpt.n
    limsupubuz
    wph
    @11
    @2
    vy
    cr
    wph
    @10
    @1
    vj
    cZ
    limsupubuzmpt.j
    wph
    @7
    cZ
    wcel
    wa
    @9
    cB
    @0
    cle
    wph
    vj
    cZ
    cB
    @8
    cr
    @8
    @8
    wceq
    wph
    @12
    a1i
    limsupubuzmpt.b
    fvmpt2d
    breq1d
    ralbida
    rexbidv
    mpbid
    @2
    @6
    vy
    vx
    cr
    @0
    @4
    wceq
    @1
    @5
    vj
    cZ
    @0
    @4
    cB
    cle
    breq2
    ralbidv
    cbvrexv
    sylib
end

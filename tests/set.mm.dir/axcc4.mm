include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wfn.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "wf.mm"
include "rabex.mm"
include "axcc3.mm"
include "rabn0.mm"
include "pm2.27.mm"
include "sylbir.mm"
include "elrab.mm"
include "syl6ib.mm"
include "ral2imi.mm"
include "simpl.mm"
include "ralimi.mm"
include "syl6.mm"
include "anim2d.mm"
include "ffnfv.mm"
include "syl6ibr.mm"
include "simpr.mm"
include "adantld.mm"
include "jcad.mm"
include "eximdv.mm"
include "mpi.mm"

theorem axcc4
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cN: class N
  assume axcc4.1: |- A e. _V
  assume axcc4.2: |- N ~~ _om
  assume axcc4.3: |- ( x = ( f ` n ) -> ( ph <-> ps ) )

  disjoint A f
  disjoint A n
  disjoint A x
  disjoint f n
  disjoint f x
  disjoint n x
  disjoint N f
  disjoint N n
  disjoint f ph
  disjoint ps x
  assert |- ( A. n e. N E. x e. A ph -> E. f ( f : N --> A /\ A. n e. N ps ) )

  proof
    wph
    vx
    cA
    wrex
    #
    vn
    cN
    wral
    #
    vf
    cv
    #
    cN
    wfn
    #
    wph
    vx
    cA
    crab
    #
    c0
    wne
    #
    vn
    cv
    @2
    cfv
    #
    @4
    wcel
    #
    wi
    #
    vn
    cN
    wral
    #
    wa
    #
    vf
    wex
    cN
    cA
    @2
    wf
    #
    wps
    vn
    cN
    wral
    #
    wa
    #
    vf
    wex
    vf
    vn
    @4
    cN
    wph
    vx
    cA
    axcc4.1
    rabex
    axcc4.2
    axcc3
    @1
    @10
    @13
    vf
    @1
    @10
    @11
    @12
    @1
    @10
    @3
    @6
    cA
    wcel
    #
    vn
    cN
    wral
    #
    wa
    @11
    @1
    @9
    @15
    @3
    @1
    @9
    @14
    wps
    wa
    #
    vn
    cN
    wral
    #
    @15
    @0
    @8
    @16
    vn
    cN
    @0
    @8
    @7
    @16
    @0
    @5
    @8
    @7
    wi
    wph
    vx
    cA
    rabn0
    @5
    @7
    pm2.27
    sylbir
    wph
    wps
    vx
    @6
    cA
    axcc4.3
    elrab
    syl6ib
    ral2imi
    #
    @16
    @14
    vn
    cN
    @14
    wps
    simpl
    ralimi
    syl6
    anim2d
    vn
    cN
    cA
    @2
    ffnfv
    syl6ibr
    @1
    @9
    @12
    @3
    @1
    @9
    @17
    @12
    @18
    @16
    wps
    vn
    cN
    @14
    wps
    simpr
    ralimi
    syl6
    adantld
    jcad
    eximdv
    mpi
end

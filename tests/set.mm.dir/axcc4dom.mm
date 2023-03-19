include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "csdm.mm"
include "cen.mm"
include "wo.mm"
include "wi.mm"
include "brdom2.mm"
include "cfn.mm"
include "wcel.mm"
include "isfinite.mm"
include "ac6sfi.mm"
include "ex.mm"
include "sylbir.mm"
include "cif.mm"
include "wceq.mm"
include "raleq.mm"
include "feq2.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "breq1.mm"
include "omex.mm"
include "enref.mm"
include "elimhyp.mm"
include "axcc4.mm"
include "dedth.mm"
include "jaoi.mm"
include "sylbi.mm"
include "imp.mm"

theorem axcc4dom
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vn: setvar n
  let cN: class N
  assume axcc4dom.1: |- A e. _V
  assume axcc4dom.2: |- ( x = ( f ` n ) -> ( ph <-> ps ) )

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
  assert |- ( ( N ~<_ _om /\ A. n e. N E. x e. A ph ) -> E. f ( f : N --> A /\ A. n e. N ps ) )

  proof
    cN
    com
    cdom
    wbr
    #
    wph
    vx
    cA
    wrex
    #
    vn
    cN
    wral
    #
    cN
    cA
    vf
    cv
    #
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
    #
    @0
    cN
    com
    csdm
    wbr
    #
    cN
    com
    cen
    wbr
    #
    wo
    @2
    @7
    wi
    #
    cN
    com
    brdom2
    @8
    @10
    @9
    @8
    cN
    cfn
    wcel
    #
    @10
    cN
    isfinite
    @11
    @2
    @7
    wph
    wps
    vn
    vx
    cN
    cA
    vf
    axcc4dom.2
    ac6sfi
    ex
    sylbir
    @9
    @10
    @1
    vn
    @9
    cN
    com
    cif
    #
    wral
    #
    @12
    cA
    @3
    wf
    #
    wps
    vn
    @12
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    cN
    com
    cN
    @12
    wceq
    #
    @2
    @13
    @7
    @17
    @1
    vn
    cN
    @12
    raleq
    @18
    @6
    @16
    vf
    @18
    @4
    @14
    @5
    @15
    cN
    @12
    cA
    @3
    feq2
    wps
    vn
    cN
    @12
    raleq
    anbi12d
    exbidv
    imbi12d
    wph
    wps
    vx
    cA
    vf
    vn
    @12
    axcc4dom.1
    @9
    @12
    com
    cen
    wbr
    com
    com
    cen
    wbr
    cN
    com
    cN
    @12
    com
    cen
    breq1
    com
    @12
    com
    cen
    breq1
    com
    omex
    enref
    elimhyp
    axcc4dom.2
    axcc4
    dedth
    jaoi
    sylbi
    imp
end

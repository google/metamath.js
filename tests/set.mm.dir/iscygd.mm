include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "ccyg.mm"
include "wrex.mm"
include "wral.mm"
include "ralrimiva.mm"
include "wa.mm"
include "wb.mm"
include "eqid.mm"
include "iscyggen2.mm"
include "syl.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "iscyg2.mm"
include "sylanbrc.mm"

theorem iscygd
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vx: setvar x
  let cE: class E
  let cN: class N
  let cO: class O
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )
  assume iscygd.3: |- ( ph -> G e. Grp )
  assume iscygd.4: |- ( ph -> X e. B )
  assume iscygd.5: |- ( ( ph /\ y e. B ) -> E. n e. ZZ y = ( n .x. X ) )

  disjoint n y
  disjoint B n
  disjoint B y
  disjoint X n
  disjoint X y
  disjoint G n
  disjoint G y
  disjoint ph y
  disjoint .x. n
  disjoint .x. y
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint B m
  disjoint n x
  disjoint x y
  disjoint B x
  disjoint E m
  disjoint E y
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint O n
  disjoint X m
  disjoint X x
  disjoint G g
  disjoint G m
  disjoint G x
  disjoint .x. g
  disjoint .x. m
  disjoint .x. x
  assert |- ( ph -> G e. CycGrp )

  proof
    wph
    cG
    cgrp
    wcel
    #
    vn
    cz
    vn
    cv
    #
    vx
    cv
    c.x
    co
    cmpt
    crn
    cB
    wceq
    vx
    cB
    crab
    #
    c0
    wne
    #
    cG
    ccyg
    wcel
    iscygd.3
    wph
    cX
    @2
    wcel
    #
    @3
    wph
    @4
    cX
    cB
    wcel
    #
    vy
    cv
    @1
    cX
    c.x
    co
    wceq
    vn
    cz
    wrex
    #
    vy
    cB
    wral
    #
    iscygd.4
    wph
    @6
    vy
    cB
    iscygd.5
    ralrimiva
    wph
    @0
    @4
    @5
    @7
    wa
    wb
    iscygd.3
    vx
    vy
    cB
    c.x
    vn
    @2
    cG
    cX
    iscyg.1
    iscyg.2
    @2
    eqid
    #
    iscyggen2
    syl
    mpbir2and
    @2
    cX
    ne0i
    syl
    vx
    cB
    c.x
    vn
    @2
    cG
    iscyg.1
    iscyg.2
    @8
    iscyg2
    sylanbrc
end

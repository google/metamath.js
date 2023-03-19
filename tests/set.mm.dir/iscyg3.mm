include "ccyg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cz.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "iscyg.mm"
include "wss.mm"
include "wf.mm"
include "wb.mm"
include "mulgcl.mm"
include "3expa.mm"
include "an32s.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "eqss.mm"
include "baib.mm"
include "3syl.mm"
include "dfss3.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "ralbii.mm"
include "bitri.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "pm5.32i.mm"

theorem iscyg3
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cG: class G
  let vg: setvar g
  let vm: setvar m
  let cE: class E
  let cN: class N
  let cO: class O
  let cX: class X
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )

  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint .x. n
  disjoint .x. x
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
  disjoint E m
  disjoint E y
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint O n
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint G g
  disjoint G m
  disjoint ph y
  disjoint .x. g
  disjoint .x. m
  assert |- ( G e. CycGrp <-> ( G e. Grp /\ E. x e. B A. y e. B E. n e. ZZ y = ( n .x. x ) ) )

  proof
    cG
    ccyg
    wcel
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
    #
    c.x
    co
    #
    cmpt
    #
    crn
    #
    cB
    wceq
    #
    vx
    cB
    wrex
    #
    wa
    @0
    vy
    cv
    #
    @3
    wceq
    vn
    cz
    wrex
    #
    vy
    cB
    wral
    #
    vx
    cB
    wrex
    #
    wa
    vx
    cB
    c.x
    vn
    cG
    iscyg.1
    iscyg.2
    iscyg
    @0
    @7
    @11
    @0
    @6
    @10
    vx
    cB
    @0
    @2
    cB
    wcel
    #
    wa
    #
    @6
    cB
    @5
    wss
    #
    @10
    @13
    cz
    cB
    @4
    wf
    @5
    cB
    wss
    #
    @6
    @14
    wb
    @13
    vn
    cz
    @3
    cB
    @4
    @0
    @1
    cz
    wcel
    #
    @12
    @3
    cB
    wcel
    #
    @0
    @16
    @12
    @17
    cB
    c.x
    cG
    @1
    @2
    iscyg.1
    iscyg.2
    mulgcl
    3expa
    an32s
    @4
    eqid
    #
    fmptd
    cz
    cB
    @4
    frn
    @6
    @15
    @14
    @5
    cB
    eqss
    baib
    3syl
    @14
    @8
    @5
    wcel
    #
    vy
    cB
    wral
    @10
    vy
    cB
    @5
    dfss3
    @19
    @9
    vy
    cB
    vn
    cz
    @3
    @8
    @4
    @18
    @1
    @2
    c.x
    ovex
    elrnmpti
    ralbii
    bitri
    syl6bb
    rexbidva
    pm5.32i
    bitri
end

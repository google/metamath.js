include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "cgrp.mm"
include "wrex.mm"
include "wral.mm"
include "iscyggen.mm"
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
include "pm5.32da.mm"
include "syl5bb.mm"

theorem iscyggen2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let cN: class N
  let cO: class O
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )
  assume iscyg3.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }

  disjoint n x
  disjoint n y
  disjoint B n
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint E y
  disjoint X n
  disjoint X x
  disjoint X y
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
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint O n
  disjoint X m
  disjoint G g
  disjoint G m
  disjoint ph y
  disjoint .x. g
  disjoint .x. m
  assert |- ( G e. Grp -> ( X e. E <-> ( X e. B /\ A. y e. B E. n e. ZZ y = ( n .x. X ) ) ) )

  proof
    cX
    cE
    wcel
    cX
    cB
    wcel
    #
    vn
    cz
    vn
    cv
    #
    cX
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
    wa
    cG
    cgrp
    wcel
    #
    @0
    vy
    cv
    #
    @2
    wceq
    vn
    cz
    wrex
    #
    vy
    cB
    wral
    #
    wa
    vx
    cB
    c.x
    vn
    cE
    cG
    cX
    iscyg.1
    iscyg.2
    iscyg3.e
    iscyggen
    @6
    @0
    @5
    @9
    @6
    @0
    wa
    #
    @5
    cB
    @4
    wss
    #
    @9
    @10
    cz
    cB
    @3
    wf
    @4
    cB
    wss
    #
    @5
    @11
    wb
    @10
    vn
    cz
    @2
    cB
    @3
    @6
    @1
    cz
    wcel
    #
    @0
    @2
    cB
    wcel
    #
    @6
    @13
    @0
    @14
    cB
    c.x
    cG
    @1
    cX
    iscyg.1
    iscyg.2
    mulgcl
    3expa
    an32s
    @3
    eqid
    #
    fmptd
    cz
    cB
    @3
    frn
    @5
    @12
    @11
    @4
    cB
    eqss
    baib
    3syl
    @11
    @7
    @4
    wcel
    #
    vy
    cB
    wral
    @9
    vy
    cB
    @4
    dfss3
    @16
    @8
    vy
    cB
    vn
    cz
    @2
    @7
    @3
    @15
    @1
    cX
    c.x
    ovex
    elrnmpti
    ralbii
    bitri
    syl6bb
    pm5.32da
    syl5bb
end

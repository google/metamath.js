include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "cgrp.mm"
include "cfn.mm"
include "cfv.mm"
include "chash.mm"
include "iscyggen.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "wss.mm"
include "simplr.mm"
include "wf.mm"
include "simplll.mm"
include "simpr.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashen.mm"
include "cc0.mm"
include "cif.mm"
include "dfod2.mm"
include "adantlr.mm"
include "iftrued.mm"
include "eqtr2d.mm"
include "eqeq1d.mm"
include "fisseneq.mm"
include "3expia.mm"
include "enrefg.mm"
include "adantr.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "3bitr3rd.mm"
include "pm5.32da.mm"
include "syl5bb.mm"

theorem cyggenod
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cO: class O
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cN: class N
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )
  assume iscyg3.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }
  assume cyggenod.o: |- O = ( od ` G )

  disjoint n x
  disjoint B n
  disjoint B x
  disjoint O n
  disjoint X n
  disjoint X x
  disjoint G n
  disjoint G x
  disjoint .x. n
  disjoint .x. x
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint B m
  disjoint n y
  disjoint x y
  disjoint B y
  disjoint E m
  disjoint E y
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint X m
  disjoint X y
  disjoint G g
  disjoint G m
  disjoint G y
  disjoint ph y
  disjoint .x. g
  disjoint .x. m
  disjoint .x. y
  assert |- ( ( G e. Grp /\ B e. Fin ) -> ( X e. E <-> ( X e. B /\ ( O ` X ) = ( # ` B ) ) ) )

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
    cB
    cfn
    wcel
    #
    wa
    #
    @0
    cX
    cO
    cfv
    #
    cB
    chash
    cfv
    #
    wceq
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
    @8
    @0
    @5
    @11
    @8
    @0
    wa
    #
    @4
    chash
    cfv
    #
    @10
    wceq
    #
    @4
    cB
    cen
    wbr
    #
    @11
    @5
    @12
    @4
    cfn
    wcel
    #
    @7
    @14
    @15
    wb
    @12
    @7
    @4
    cB
    wss
    #
    @16
    @6
    @7
    @0
    simplr
    #
    @12
    cz
    cB
    @3
    wf
    @17
    @12
    vn
    cz
    @2
    cB
    @3
    @12
    @1
    cz
    wcel
    #
    wa
    @6
    @19
    @0
    @2
    cB
    wcel
    @6
    @7
    @0
    @19
    simplll
    @12
    @19
    simpr
    @8
    @0
    @19
    simplr
    cB
    c.x
    cG
    @1
    cX
    iscyg.1
    iscyg.2
    mulgcl
    syl3anc
    @3
    eqid
    #
    fmptd
    cz
    cB
    @3
    frn
    syl
    #
    cB
    @4
    ssfi
    syl2anc
    #
    @18
    @4
    cB
    hashen
    syl2anc
    @12
    @13
    @9
    @10
    @12
    @9
    @16
    @13
    cc0
    cif
    #
    @13
    @6
    @0
    @9
    @23
    wceq
    @7
    vn
    cX
    c.x
    @3
    cG
    cO
    cB
    iscyg.1
    cyggenod.o
    iscyg.2
    @20
    dfod2
    adantlr
    @12
    @16
    @13
    cc0
    @22
    iftrued
    eqtr2d
    eqeq1d
    @12
    @7
    @17
    @15
    @5
    wb
    @18
    @21
    @7
    @17
    wa
    #
    @15
    @5
    @7
    @17
    @15
    @5
    @4
    cB
    fisseneq
    3expia
    @24
    @15
    @5
    cB
    cB
    cen
    wbr
    #
    @7
    @25
    @17
    cB
    cfn
    enrefg
    adantr
    @4
    cB
    cB
    cen
    breq1
    syl5ibrcom
    impbid
    syl2anc
    3bitr3rd
    pm5.32da
    syl5bb
end

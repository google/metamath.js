include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "wral.mm"
include "iscyggen2.mm"
include "simprbda.mm"
include "grpinvcl.mm"
include "syldan.mm"
include "simplbda.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "cneg.mm"
include "znegcl.mm"
include "adantl.mm"
include "simpr.mm"
include "zcnd.mm"
include "negnegd.mm"
include "oveq1d.mm"
include "simplll.mm"
include "ad2antrr.mm"
include "mulgneg2.mm"
include "syl3anc.mm"
include "eqtr3d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralimdva.mm"
include "mpd.mm"
include "wb.mm"
include "adantr.mm"
include "mpbir2and.mm"

theorem cyggeninv
  let vx: setvar x
  let cB: class B
  let c.x: class .x.
  let vn: setvar n
  let cE: class E
  let cG: class G
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cO: class O
  let wph: wff ph
  assume iscyg.1: |- B = ( Base ` G )
  assume iscyg.2: |- .x. = ( .g ` G )
  assume iscyg3.e: |- E = { x e. B | ran ( n e. ZZ |-> ( n .x. x ) ) = B }
  assume cyggeninv.n: |- N = ( invg ` G )

  disjoint n x
  disjoint B n
  disjoint B x
  disjoint N n
  disjoint N x
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
  disjoint N y
  disjoint O n
  disjoint X m
  disjoint X y
  disjoint G g
  disjoint G m
  disjoint G y
  disjoint ph y
  disjoint .x. g
  disjoint .x. m
  disjoint .x. y
  assert |- ( ( G e. Grp /\ X e. E ) -> ( N ` X ) e. E )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cE
    wcel
    #
    wa
    #
    cX
    cN
    cfv
    #
    cE
    wcel
    #
    @3
    cB
    wcel
    #
    vy
    cv
    #
    vn
    cv
    #
    @3
    c.x
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    vy
    cB
    wral
    #
    @0
    @1
    cX
    cB
    wcel
    #
    @5
    @0
    @1
    @12
    @6
    @7
    cX
    c.x
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    vy
    cB
    wral
    #
    vx
    vy
    cB
    c.x
    vn
    cE
    cG
    cX
    iscyg.1
    iscyg.2
    iscyg3.e
    iscyggen2
    #
    simprbda
    #
    cB
    cG
    cN
    cX
    iscyg.1
    cyggeninv.n
    grpinvcl
    syldan
    @2
    @16
    @11
    @0
    @1
    @12
    @16
    @17
    simplbda
    @2
    @15
    @10
    vy
    cB
    @15
    @6
    vm
    cv
    #
    cX
    c.x
    co
    #
    wceq
    #
    vm
    cz
    wrex
    @2
    @6
    cB
    wcel
    #
    wa
    #
    @10
    @14
    @21
    vn
    vm
    cz
    @7
    @19
    wceq
    @13
    @20
    @6
    @7
    @19
    cX
    c.x
    oveq1
    eqeq2d
    cbvrexv
    @23
    @21
    @10
    vm
    cz
    @23
    @19
    cz
    wcel
    #
    wa
    #
    @10
    @21
    @20
    @8
    wceq
    #
    vn
    cz
    wrex
    #
    @25
    @19
    cneg
    #
    cz
    wcel
    #
    @20
    @28
    @3
    c.x
    co
    #
    wceq
    #
    @27
    @24
    @29
    @23
    @19
    znegcl
    adantl
    #
    @25
    @28
    cneg
    #
    cX
    c.x
    co
    #
    @20
    @30
    @25
    @33
    @19
    cX
    c.x
    @25
    @19
    @25
    @19
    @23
    @24
    simpr
    zcnd
    negnegd
    oveq1d
    @25
    @0
    @29
    @12
    @34
    @30
    wceq
    @0
    @1
    @22
    @24
    simplll
    @32
    @2
    @12
    @22
    @24
    @18
    ad2antrr
    cB
    c.x
    cG
    cN
    @28
    cX
    iscyg.1
    iscyg.2
    cyggeninv.n
    mulgneg2
    syl3anc
    eqtr3d
    @26
    @31
    vn
    @28
    cz
    @7
    @28
    wceq
    @8
    @30
    @20
    @7
    @28
    @3
    c.x
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @21
    @9
    @26
    vn
    cz
    @6
    @20
    @8
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    syl5bi
    ralimdva
    mpd
    @0
    @4
    @5
    @11
    wa
    wb
    @1
    vx
    vy
    cB
    c.x
    vn
    cE
    cG
    @3
    iscyg.1
    iscyg.2
    iscyg3.e
    iscyggen2
    adantr
    mpbir2and
end

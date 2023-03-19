include "cabl.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "cminusg.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantr.mm"
include "simpr3.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "mulgdi.mm"
include "syl13anc.mm"
include "cneg.mm"
include "mulgneg2.mm"
include "mulgneg.mm"
include "eqtr3d.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "grpsubval.mm"
include "mulgcl.mm"
include "3eqtr4d.mm"

theorem mulgsubdi
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume mulgsubdi.b: |- B = ( Base ` G )
  assume mulgsubdi.t: |- .x. = ( .g ` G )
  assume mulgsubdi.d: |- .- = ( -g ` G )


  assert |- ( ( G e. Abel /\ ( M e. ZZ /\ X e. B /\ Y e. B ) ) -> ( M .x. ( X .- Y ) ) = ( ( M .x. X ) .- ( M .x. Y ) ) )

  proof
    cG
    cabl
    wcel
    #
    cM
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cM
    cX
    cY
    cG
    cminusg
    cfv
    #
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    c.x
    co
    #
    cM
    cX
    c.x
    co
    #
    cM
    cY
    c.x
    co
    #
    @6
    cfv
    #
    @8
    co
    #
    cM
    cX
    cY
    c.mi
    co
    #
    c.x
    co
    @11
    @12
    c.mi
    co
    #
    @5
    @10
    @11
    cM
    @7
    c.x
    co
    #
    @8
    co
    #
    @14
    @5
    @0
    @1
    @2
    @7
    cB
    wcel
    #
    @10
    @18
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @5
    cG
    cgrp
    wcel
    #
    @3
    @19
    @0
    @22
    @4
    cG
    ablgrp
    adantr
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    cG
    @6
    cY
    mulgsubdi.b
    @6
    eqid
    #
    grpinvcl
    syl2anc
    cB
    @8
    c.x
    cG
    cM
    cX
    @7
    mulgsubdi.b
    mulgsubdi.t
    @8
    eqid
    #
    mulgdi
    syl13anc
    @5
    @17
    @13
    @11
    @8
    @5
    @22
    @1
    @3
    @17
    @13
    wceq
    @23
    @20
    @24
    @22
    @1
    @3
    w3a
    cM
    cneg
    cY
    c.x
    co
    @17
    @13
    cB
    c.x
    cG
    @6
    cM
    cY
    mulgsubdi.b
    mulgsubdi.t
    @25
    mulgneg2
    cB
    c.x
    cG
    @6
    cM
    cY
    mulgsubdi.b
    mulgsubdi.t
    @25
    mulgneg
    eqtr3d
    syl3anc
    oveq2d
    eqtrd
    @5
    @15
    @9
    cM
    c.x
    @5
    @2
    @3
    @15
    @9
    wceq
    @21
    @24
    cB
    @8
    cG
    @6
    c.mi
    cX
    cY
    mulgsubdi.b
    @26
    @25
    mulgsubdi.d
    grpsubval
    syl2anc
    oveq2d
    @5
    @11
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @16
    @14
    wceq
    @5
    @22
    @1
    @2
    @27
    @23
    @20
    @21
    cB
    c.x
    cG
    cM
    cX
    mulgsubdi.b
    mulgsubdi.t
    mulgcl
    syl3anc
    @5
    @22
    @1
    @3
    @28
    @23
    @20
    @24
    cB
    c.x
    cG
    cM
    cY
    mulgsubdi.b
    mulgsubdi.t
    mulgcl
    syl3anc
    cB
    @8
    cG
    @6
    c.mi
    @11
    @12
    mulgsubdi.b
    @26
    @25
    mulgsubdi.d
    grpsubval
    syl2anc
    3eqtr4d
end

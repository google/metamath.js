include "crg.mm"
include "wcel.mm"
include "cz.mm"
include "wf1.mm"
include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "cmg.mm"
include "co.mm"
include "cmpt.mm"
include "cod.mm"
include "cc0.mm"
include "wceq.mm"
include "cchr.mm"
include "wb.mm"
include "eqid.mm"
include "zrhval2.mm"
include "f1eq1.mm"
include "syl.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "odf1.mm"
include "syl2anc.mm"
include "chrval.mm"
include "eqeq1i.mm"
include "a1i.mm"
include "3bitr2rd.mm"

theorem zrhchr
  let cB: class B
  let cR: class R
  let cL: class L
  let c.0: class .0.
  let vx: setvar x
  assume zrhker.0: |- B = ( Base ` R )
  assume zrhker.1: |- L = ( ZRHom ` R )
  assume zrhker.2: |- .0. = ( 0g ` R )


  assert |- ( R e. Ring -> ( ( chr ` R ) = 0 <-> L : ZZ -1-1-> B ) )

  proof
    cR
    crg
    wcel
    #
    cz
    cB
    cL
    wf1
    #
    cz
    cB
    vx
    cz
    vx
    cv
    cR
    cur
    cfv
    #
    cR
    cmg
    cfv
    #
    co
    cmpt
    #
    wf1
    #
    @2
    cR
    cod
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    cR
    cchr
    cfv
    #
    cc0
    wceq
    #
    @0
    cL
    @4
    wceq
    @1
    @5
    wb
    cR
    @3
    @2
    vx
    cL
    zrhker.1
    @3
    eqid
    #
    @2
    eqid
    #
    zrhval2
    cz
    cB
    cL
    @4
    f1eq1
    syl
    @0
    cR
    cgrp
    wcel
    @2
    cB
    wcel
    @8
    @5
    wb
    cR
    ringgrp
    cB
    cR
    @2
    zrhker.0
    @12
    ringidcl
    vx
    @2
    @3
    @4
    cR
    @6
    cB
    zrhker.0
    @6
    eqid
    #
    @11
    @4
    eqid
    odf1
    syl2anc
    @8
    @10
    wb
    @0
    @7
    @9
    cc0
    @9
    cR
    @2
    @6
    @13
    @12
    @9
    eqid
    chrval
    eqeq1i
    a1i
    3bitr2rd
end

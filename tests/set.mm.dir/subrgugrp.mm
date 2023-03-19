include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "csubg.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wral.mm"
include "cinvr.mm"
include "wa.mm"
include "subrguss.mm"
include "crg.mm"
include "cur.mm"
include "subrgring.mm"
include "eqid.mm"
include "1unit.mm"
include "ne0i.mm"
include "3syl.mm"
include "w3a.mm"
include "wceq.mm"
include "ressmulr.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "unitmulcl.mm"
include "syl3an1.mm"
include "eqeltrd.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "subrginv.mm"
include "unitinvcl.mm"
include "sylan.mm"
include "jca.mm"
include "cgrp.mm"
include "wb.mm"
include "subrgrcl.mm"
include "unitgrp.mm"
include "unitgrpbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cmgp.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "invrfval.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem subrgugrp
  let cA: class A
  let cR: class R
  let cS: class S
  let cU: class U
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cI: class I
  let cX: class X
  assume subrgugrp.1: |- S = ( R |`s A )
  assume subrgugrp.2: |- U = ( Unit ` R )
  assume subrgugrp.3: |- V = ( Unit ` S )
  assume subrgugrp.4: |- G = ( ( mulGrp ` R ) |`s U )


  assert |- ( A e. ( SubRing ` R ) -> V e. ( SubGrp ` G ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cV
    cG
    csubg
    cfv
    wcel
    #
    cV
    cU
    wss
    #
    cV
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cV
    wcel
    #
    vy
    cV
    wral
    #
    @5
    cR
    cinvr
    cfv
    #
    cfv
    #
    cV
    wcel
    #
    wa
    #
    vx
    cV
    wral
    #
    cA
    cR
    cS
    cU
    cV
    subrgugrp.1
    subrgugrp.2
    subrgugrp.3
    subrguss
    @1
    cS
    crg
    wcel
    #
    cS
    cur
    cfv
    #
    cV
    wcel
    @4
    cA
    cR
    cS
    subrgugrp.1
    subrgring
    #
    cS
    cV
    @17
    subrgugrp.3
    @17
    eqid
    1unit
    cV
    @17
    ne0i
    3syl
    @1
    @14
    vx
    cV
    @1
    @5
    cV
    wcel
    #
    wa
    #
    @10
    @13
    @20
    @9
    vy
    cV
    @1
    @19
    @6
    cV
    wcel
    #
    @9
    @1
    @19
    @21
    w3a
    #
    @8
    @5
    @6
    cS
    cmulr
    cfv
    #
    co
    #
    cV
    @22
    @7
    @23
    @5
    @6
    @1
    @19
    @7
    @23
    wceq
    @21
    cA
    cR
    cS
    @7
    @0
    subrgugrp.1
    @7
    eqid
    #
    ressmulr
    3ad2ant1
    oveqd
    @1
    @16
    @19
    @21
    @24
    cV
    wcel
    @18
    cS
    @23
    cV
    @5
    @6
    subrgugrp.3
    @23
    eqid
    unitmulcl
    syl3an1
    eqeltrd
    3expa
    ralrimiva
    @20
    @12
    @5
    cS
    cinvr
    cfv
    #
    cfv
    #
    cV
    cA
    cR
    cS
    cV
    @11
    @26
    @5
    subrgugrp.1
    @11
    eqid
    #
    subrgugrp.3
    @26
    eqid
    #
    subrginv
    @1
    @16
    @19
    @27
    cV
    wcel
    @18
    cS
    cV
    @26
    @5
    subrgugrp.3
    @29
    unitinvcl
    sylan
    eqeltrd
    jca
    ralrimiva
    @1
    cR
    crg
    wcel
    cG
    cgrp
    wcel
    @2
    @3
    @4
    @15
    w3a
    wb
    cA
    cR
    subrgrcl
    cR
    cU
    cG
    subrgugrp.2
    subrgugrp.4
    unitgrp
    vx
    vy
    cU
    @7
    cV
    cG
    @11
    cR
    cU
    cG
    subrgugrp.2
    subrgugrp.4
    unitgrpbas
    cU
    cvv
    wcel
    @7
    cG
    cplusg
    cfv
    wceq
    cU
    cR
    cui
    cfv
    cvv
    subrgugrp.2
    cR
    cui
    fvex
    eqeltri
    cU
    @7
    cR
    cmgp
    cfv
    #
    cG
    cvv
    subrgugrp.4
    cR
    @7
    @30
    @30
    eqid
    @25
    mgpplusg
    ressplusg
    ax-mp
    cR
    cU
    cG
    @11
    subrgugrp.2
    subrgugrp.4
    @28
    invrfval
    issubg2
    3syl
    mpbir3and
end

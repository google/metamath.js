include "wcel.mm"
include "cfv.mm"
include "ccnv.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "wf1o.mm"
include "elsymgbas2.mm"
include "ibi.mm"
include "f1ocnv.mm"
include "syl.mm"
include "cvv.mm"
include "wb.mm"
include "cnvexg.mm"
include "mpbird.mm"
include "eqid.mm"
include "symgov.mm"
include "mpdan.mm"
include "f1ococnv2.mm"
include "csymg.mm"
include "elbasfv.mm"
include "symgid.mm"
include "3eqtrd.mm"
include "cgrp.mm"
include "symggrp.mm"
include "id.mm"
include "grpinvid1.mm"
include "syl3anc.mm"

theorem symginv
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cN: class N
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  assume symggrp.1: |- G = ( SymGrp ` A )
  assume symginv.2: |- B = ( Base ` G )
  assume symginv.3: |- N = ( invg ` G )


  assert |- ( F e. B -> ( N ` F ) = `' F )

  proof
    cF
    cB
    wcel
    #
    cF
    cN
    cfv
    cF
    ccnv
    #
    wceq
    #
    cF
    @1
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    @0
    @4
    cF
    @1
    ccom
    #
    cid
    cA
    cres
    #
    @5
    @0
    @1
    cB
    wcel
    #
    @4
    @7
    wceq
    @0
    @9
    cA
    cA
    @1
    wf1o
    #
    @0
    cA
    cA
    cF
    wf1o
    #
    @10
    @0
    @11
    cA
    cB
    cF
    cG
    cB
    symggrp.1
    symginv.2
    elsymgbas2
    ibi
    #
    cA
    cA
    cF
    f1ocnv
    syl
    @0
    @1
    cvv
    wcel
    @9
    @10
    wb
    cF
    cB
    cnvexg
    cA
    cB
    @1
    cG
    cvv
    symggrp.1
    symginv.2
    elsymgbas2
    syl
    mpbird
    #
    cA
    cB
    @3
    cG
    cF
    @1
    symggrp.1
    symginv.2
    @3
    eqid
    #
    symgov
    mpdan
    @0
    @11
    @7
    @8
    wceq
    @12
    cA
    cA
    cF
    f1ococnv2
    syl
    @0
    cA
    cvv
    wcel
    #
    @8
    @5
    wceq
    cB
    cG
    csymg
    cF
    cA
    symggrp.1
    symginv.2
    elbasfv
    #
    cA
    cG
    cvv
    symggrp.1
    symgid
    syl
    3eqtrd
    @0
    cG
    cgrp
    wcel
    #
    @0
    @9
    @2
    @6
    wb
    @0
    @15
    @17
    @16
    cA
    cG
    cvv
    symggrp.1
    symggrp
    syl
    @0
    id
    @13
    cB
    @3
    cG
    cN
    cF
    @1
    @5
    symginv.2
    @14
    @5
    eqid
    symginv.3
    grpinvid1
    syl3anc
    mpbird
end

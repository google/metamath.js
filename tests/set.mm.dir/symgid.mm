include "wcel.mm"
include "c0g.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "ccom.mm"
include "cbs.mm"
include "wf1o.mm"
include "f1oi.mm"
include "eqid.mm"
include "elsymgbas.mm"
include "mpbiri.mm"
include "symgov.mm"
include "syl2anc.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi1.mm"
include "mp2b.mm"
include "syl6eq.mm"
include "cgrp.mm"
include "wb.mm"
include "symggrp.mm"
include "grpid.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem symgid
  let cA: class A
  let cG: class G
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume symggrp.1: |- G = ( SymGrp ` A )


  assert |- ( A e. V -> ( _I |` A ) = ( 0g ` G ) )

  proof
    cA
    cV
    wcel
    #
    cG
    c0g
    cfv
    #
    cid
    cA
    cres
    #
    @0
    @2
    @2
    cG
    cplusg
    cfv
    #
    co
    #
    @2
    wceq
    #
    @1
    @2
    wceq
    #
    @0
    @4
    @2
    @2
    ccom
    #
    @2
    @0
    @2
    cG
    cbs
    cfv
    #
    wcel
    #
    @9
    @4
    @7
    wceq
    @0
    @9
    cA
    cA
    @2
    wf1o
    #
    cA
    f1oi
    #
    cA
    @8
    @2
    cG
    cV
    symggrp.1
    @8
    eqid
    #
    elsymgbas
    mpbiri
    #
    @13
    cA
    @8
    @3
    cG
    @2
    @2
    symggrp.1
    @12
    @3
    eqid
    #
    symgov
    syl2anc
    @10
    cA
    cA
    @2
    wf
    @7
    @2
    wceq
    @11
    cA
    cA
    @2
    f1of
    cA
    cA
    @2
    fcoi1
    mp2b
    syl6eq
    @0
    cG
    cgrp
    wcel
    @9
    @5
    @6
    wb
    cA
    cG
    cV
    symggrp.1
    symggrp
    @13
    @8
    @3
    cG
    @2
    @1
    @12
    @14
    @1
    eqid
    grpid
    syl2anc
    mpbid
    eqcomd
end
